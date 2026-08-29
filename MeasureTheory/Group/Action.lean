/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Dynamics.Minimal
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Group.Defs

/-!
# Measures invariant under group actions

A measure `μ : Measure α` is said to be *invariant* under an action of a group `G` if scalar
multiplication by `c : G` is a measure-preserving map for all `c`. In this file we define a
typeclass for measures invariant under action of an (additive or multiplicative) group and prove
some basic properties of such measures.
-/

public section


open scoped ENNReal NNReal Pointwise Topology symmDiff
open MeasureTheory.Measure Set Function Filter

namespace MeasureTheory

universe u v w

variable {G : Type u} {M : Type v} {α : Type w}

namespace SMulInvariantMeasure

@[to_additive]
/--
Instance `zero` / 实例 `zero`

English:
instance zero
  signature: [MeasurableSpace α] [SMul M α]
  body: ⟨fun _ _ _ => rfl⟩

中文:
实例 zero
  签名: [可测空间 α] [标量乘法 M α]
  定义体: ⟨fun _ _ _ => rfl⟩
-/
instance zero [MeasurableSpace α] [SMul M α] : SMulInvariantMeasure M α (0 : Measure α) :=
  ⟨fun _ _ _ => rfl⟩

variable [SMul M α] {m : MeasurableSpace α} {μ ν : Measure α}

@[to_additive]
/--
Instance `add` / 实例 `add`

English:
instance add
  signature: [SMulInvariantMeasure M α μ] [SMulInvariantMeasure M α ν]
  body: ⟨fun c _s hs =>
    show _ + _ = _ + _ from
      congr_arg₂ (· + ·) (measure_preimage_smul c hs) (measure_preimage_smul c hs)⟩

@[to_additive]

中文:
实例 add
  签名: [标量乘不变测度 M α μ] [标量乘不变测度 M α ν]
  定义体: ⟨fun c _s hs =>
    show _ + _ = _ + _ from
      congr_arg₂ (· + ·) (measure_preimage_smul c hs) (measure_preimage_smul c hs)⟩

@[to_additive]

Depends on / 依赖: measure_preimage_smul
-/
instance add [SMulInvariantMeasure M α μ] [SMulInvariantMeasure M α ν] :
    SMulInvariantMeasure M α (μ + ν) :=
  ⟨fun c _s hs =>
    show _ + _ = _ + _ from
      congr_arg₂ (· + ·) (measure_preimage_smul c hs) (measure_preimage_smul c hs)⟩

@[to_additive]
/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: [SMulInvariantMeasure M α μ] (c : Real>=0∞)
  body: ⟨fun a _s hs => show c • _ = c • _ from congr_arg (c • ·) (measure_preimage_smul a hs)⟩

@[to_additive]

中文:
实例 smul
  签名: [标量乘不变测度 M α μ] (c : 实数>=0∞)
  定义体: ⟨fun a _s hs => show c • _ = c • _ from congr_arg (c • ·) (measure_preimage_smul a hs)⟩

@[to_additive]

Depends on / 依赖: congr_arg, measure_preimage_smul
-/
instance smul [SMulInvariantMeasure M α μ] (c : Real>=0∞) : SMulInvariantMeasure M α (c • μ) :=
  ⟨fun a _s hs => show c • _ = c • _ from congr_arg (c • ·) (measure_preimage_smul a hs)⟩

@[to_additive]
/--
Instance `smul_nnreal` / 实例 `smul_nnreal`

English:
instance smul_nnreal
  signature: [SMulInvariantMeasure M α μ] (c : Real>=0)
  body: SMulInvariantMeasure.smul c

中文:
实例 smul_nnreal
  签名: [标量乘不变测度 M α μ] (c : 实数>=0)
  定义体: SMulInvariantMeasure.smul c

Depends on / 依赖: SMulInvariantMeasure, SMulInvariantMeasure.smul
-/
instance smul_nnreal [SMulInvariantMeasure M α μ] (c : Real>=0) : SMulInvariantMeasure M α (c • μ) :=
  SMulInvariantMeasure.smul c

end SMulInvariantMeasure

section AE_smul

variable {m : MeasurableSpace α} [SMul G α]
  (μ : Measure α) [SMulInvariantMeasure G α μ] {s : Set α}

/-- See also `measure_preimage_smul_of_nullMeasurableSet` and `measure_preimage_smul`. -/
@[to_additive
/-- See also `measure_preimage_smul_of_nullMeasurableSet` and `measure_preimage_smul`. -/]
/--
theorem `measure_preimage_smul_le` / 定理 `measure_preimage_smul_le`

English:
theorem measure_preimage_smul_le
  given: (c : G) (s : Set α)
  statement: μ ((c • ·) ⁻¹' s) <= μ s
  proof: (outerMeasure_le_iff (m := .map (c • ·) μ.1)).2
    (fun _s hs => (SMulInvariantMeasure.measure_preimage_smul _ hs).le) _

中文:
定理 measure_preimage_smul_le
  条件: (c : G) (s : 集合 α)
  结论: μ ((c • ·) ⁻¹' s) <= μ s
  证明: (outerMeasure_le_iff (m := .map (c • ·) μ.1)).2
    (fun _s hs => (SMulInvariantMeasure.measure_preimage_smul _ hs).le) _

Depends on / 依赖: SMulInvariantMeasure, SMulInvariantMeasure.measure_preimage_smul, measure_preimage_smul, outerMeasure_le_iff
-/
theorem measure_preimage_smul_le (c : G) (s : Set α) : μ ((c • ·) ⁻¹' s) <= μ s :=
  (outerMeasure_le_iff (m := .map (c • ·) μ.1)).2
    (fun _s hs => (SMulInvariantMeasure.measure_preimage_smul _ hs).le) _

/-- See also `smul_ae`. -/
@[to_additive /-- See also `vadd_ae`. -/]
/--
theorem `tendsto_smul_ae` / 定理 `tendsto_smul_ae`

English:
theorem tendsto_smul_ae
  given: (c : G)
  statement: Filter.Tendsto (c • ·) (ae μ) (ae μ)
  proof: fun _s hs =>
  eq_bot_mono (measure_preimage_smul_le μ c _) hs

中文:
定理 tendsto_smul_ae
  条件: (c : G)
  结论: 滤子.收敛 (c • ·) (ae μ) (ae μ)
  证明: fun _s hs =>
  eq_bot_mono (measure_preimage_smul_le μ c _) hs
-/
theorem tendsto_smul_ae (c : G) : Filter.Tendsto (c • ·) (ae μ) (ae μ) := fun _s hs =>
  eq_bot_mono (measure_preimage_smul_le μ c _) hs

variable {μ}

@[to_additive]
/--
theorem `measure_preimage_smul_null` / 定理 `measure_preimage_smul_null`

English:
theorem measure_preimage_smul_null
  given: (h : μ s = 0) (c : G)
  statement: μ ((c • ·) ⁻¹' s) = 0
  proof: eq_bot_mono (measure_preimage_smul_le μ c _) h

@[to_additive]

中文:
定理 measure_preimage_smul_null
  条件: (h : μ s = 0) (c : G)
  结论: μ ((c • ·) ⁻¹' s) = 0
  证明: eq_bot_mono (measure_preimage_smul_le μ c _) h

@[to_additive]

Depends on / 依赖: eq_bot_mono, measure_preimage_smul_le
-/
theorem measure_preimage_smul_null (h : μ s = 0) (c : G) : μ ((c • ·) ⁻¹' s) = 0 :=
  eq_bot_mono (measure_preimage_smul_le μ c _) h

@[to_additive]
/--
theorem `measure_preimage_smul_of_nullMeasurableSet` / 定理 `measure_preimage_smul_of_nullMeasurableSet`

English:
theorem measure_preimage_smul_of_nullMeasurableSet
  given: (hs : NullMeasurableSet s μ) (c : G)
  proof: by
  rw [← measure_toMeasurable s]; rw [← SMulInvariantMeasure.measure_preimage_smul c (measurableSet_toMeasurable μ s)]
.symm exact measure_congr (tendsto_smul_ae μ c hs.toMeasurable_ae_eq)

中文:
定理 measure_preimage_smul_of_nullMeasurableSet
  条件: (hs : NullMeasurableSet s μ) (c : G)
  证明: by
  rw [← measure_toMeasurable s]; rw [← SMulInvariantMeasure.measure_preimage_smul c (measurableSet_toMeasurable μ s)]
.symm exact measure_congr (tendsto_smul_ae μ c hs.toMeasurable_ae_eq)

Depends on / 依赖: SMulInvariantMeasure, SMulInvariantMeasure.measure_preimage_smul, hs.toMeasurable_ae_eq, measurableSet_toMeasurable, measure_congr, measure_preimage_smul, measure_toMeasurable, tendsto_smul_ae, toMeasurable_ae_eq
-/
theorem measure_preimage_smul_of_nullMeasurableSet (hs : NullMeasurableSet s μ) (c : G) :
    μ ((c • ·) ⁻¹' s) = μ s := by
  rw [← measure_toMeasurable s]; rw [← SMulInvariantMeasure.measure_preimage_smul c (measurableSet_toMeasurable μ s)]
.symm exact measure_congr (tendsto_smul_ae μ c hs.toMeasurable_ae_eq)

end AE_smul

section AE

variable {m : MeasurableSpace α} [Group G] [MulAction G α]
  (μ : Measure α) [SMulInvariantMeasure G α μ]

@[to_additive (attr := simp)]
/--
theorem `measure_preimage_smul` / 定理 `measure_preimage_smul`

English:
theorem measure_preimage_smul
  given: (c : G) (s : Set α)
  statement: μ ((c • ·) ⁻¹' s) = μ s
  proof: (measure_preimage_smul_le μ c s).antisymm by
    simpa [preimage_preimage] using measure_preimage_smul_le μ c⁻¹ ((c • ·) ⁻¹' s)

@[to_additive (attr := simp)]

中文:
定理 measure_preimage_smul
  条件: (c : G) (s : 集合 α)
  结论: μ ((c • ·) ⁻¹' s) = μ s
  证明: (measure_preimage_smul_le μ c s).antisymm by
    simpa [preimage_preimage] using measure_preimage_smul_le μ c⁻¹ ((c • ·) ⁻¹' s)

@[to_additive (attr := simp)]

Depends on / 依赖: antisymm, measure_preimage_smul_le, preimage_preimage
-/
theorem measure_preimage_smul (c : G) (s : Set α) : μ ((c • ·) ⁻¹' s) = μ s :=
(measure_preimage_smul_le μ c s).antisymm by
    simpa [preimage_preimage] using measure_preimage_smul_le μ c⁻¹ ((c • ·) ⁻¹' s)

@[to_additive (attr := simp)]
/--
theorem `measure_smul` / 定理 `measure_smul`

English:
theorem measure_smul
  given: (c : G) (s : Set α)
  statement: μ (c • s) = μ s
  proof: by
  simpa only [preimage_smul_inv] using measure_preimage_smul μ c⁻¹ s

@[to_additive (attr := simp)]

中文:
定理 measure_smul
  条件: (c : G) (s : 集合 α)
  结论: μ (c • s) = μ s
  证明: by
  simpa only [preimage_smul_inv] using measure_preimage_smul μ c⁻¹ s

@[to_additive (attr := simp)]

Depends on / 依赖: measure_preimage_smul, preimage_smul_inv
-/
theorem measure_smul (c : G) (s : Set α) : μ (c • s) = μ s := by
  simpa only [preimage_smul_inv] using measure_preimage_smul μ c⁻¹ s

@[to_additive (attr := simp)]
/--
theorem `measure_inter_inv_smul` / 定理 `measure_inter_inv_smul`

English:
theorem measure_inter_inv_smul
  given: (c : G) (s t : Set α)
  statement: μ (s inter c⁻¹ • t) = μ (c • s inter t)
  proof: by
  rw [← measure_smul _ c]; rw [smul_set_inter]; rw [smul_smul]; rw [mul_inv_cancel]; rw [one_smul]

@[to_additive (attr := simp)]

中文:
定理 measure_inter_inv_smul
  条件: (c : G) (s t : 集合 α)
  结论: μ (s inter c⁻¹ • t) = μ (c • s inter t)
  证明: by
  rw [← measure_smul _ c]; rw [smul_set_inter]; rw [smul_smul]; rw [mul_inv_cancel]; rw [one_smul]

@[to_additive (attr := simp)]

Depends on / 依赖: measure_smul, mul_inv_cancel, one_smul, smul_set_inter, smul_smul
-/
theorem measure_inter_inv_smul (c : G) (s t : Set α) : μ (s inter c⁻¹ • t) = μ (c • s inter t) := by
  rw [← measure_smul _ c]; rw [smul_set_inter]; rw [smul_smul]; rw [mul_inv_cancel]; rw [one_smul]

@[to_additive (attr := simp)]
/--
theorem `measure_inv_smul_inter` / 定理 `measure_inv_smul_inter`

English:
theorem measure_inv_smul_inter
  given: (c : G) (s t : Set α)
  statement: μ (c⁻¹ • s inter t) = μ (s inter c • t)
  proof: by
  simpa [inv_inv] using (measure_inter_inv_smul _ c⁻¹ _ _).symm

@[to_additive (attr := simp)]

中文:
定理 measure_inv_smul_inter
  条件: (c : G) (s t : 集合 α)
  结论: μ (c⁻¹ • s inter t) = μ (s inter c • t)
  证明: by
  simpa [inv_inv] using (measure_inter_inv_smul _ c⁻¹ _ _).symm

@[to_additive (attr := simp)]

Depends on / 依赖: inv_inv, measure_inter_inv_smul
-/
theorem measure_inv_smul_inter (c : G) (s t : Set α) : μ (c⁻¹ • s inter t) = μ (s inter c • t) := by
  simpa [inv_inv] using (measure_inter_inv_smul _ c⁻¹ _ _).symm

@[to_additive (attr := simp)]
/--
theorem `measure_union_inv_smul` / 定理 `measure_union_inv_smul`

English:
theorem measure_union_inv_smul
  given: (c : G) (s t : Set α)
  statement: μ (s union c⁻¹ • t) = μ (c • s union t)
  proof: by
  rw [← measure_smul _ c]; rw [smul_set_union]; rw [smul_smul]; rw [mul_inv_cancel]; rw [one_smul]

@[to_additive (attr := simp)]

中文:
定理 measure_union_inv_smul
  条件: (c : G) (s t : 集合 α)
  结论: μ (s union c⁻¹ • t) = μ (c • s union t)
  证明: by
  rw [← measure_smul _ c]; rw [smul_set_union]; rw [smul_smul]; rw [mul_inv_cancel]; rw [one_smul]

@[to_additive (attr := simp)]

Depends on / 依赖: measure_smul, mul_inv_cancel, one_smul, smul_set_union, smul_smul
-/
theorem measure_union_inv_smul (c : G) (s t : Set α) : μ (s union c⁻¹ • t) = μ (c • s union t) := by
  rw [← measure_smul _ c]; rw [smul_set_union]; rw [smul_smul]; rw [mul_inv_cancel]; rw [one_smul]

@[to_additive (attr := simp)]
/--
theorem `measure_inv_smul_union` / 定理 `measure_inv_smul_union`

English:
theorem measure_inv_smul_union
  given: (c : G) (s t : Set α)
  statement: μ (c⁻¹ • s union t) = μ (s union c • t)
  proof: by
  simpa [inv_inv] using (measure_union_inv_smul _ c⁻¹ _ _).symm

@[to_additive (attr := simp)]

中文:
定理 measure_inv_smul_union
  条件: (c : G) (s t : 集合 α)
  结论: μ (c⁻¹ • s union t) = μ (s union c • t)
  证明: by
  simpa [inv_inv] using (measure_union_inv_smul _ c⁻¹ _ _).symm

@[to_additive (attr := simp)]

Depends on / 依赖: inv_inv, measure_union_inv_smul
-/
theorem measure_inv_smul_union (c : G) (s t : Set α) : μ (c⁻¹ • s union t) = μ (s union c • t) := by
  simpa [inv_inv] using (measure_union_inv_smul _ c⁻¹ _ _).symm

@[to_additive (attr := simp)]
/--
theorem `measure_sdiff_inv_smul` / 定理 `measure_sdiff_inv_smul`

English:
theorem measure_sdiff_inv_smul
  given: (c : G) (s t : Set α)
  statement: μ (s \ c⁻¹ • t) = μ (c • s \ t)
  proof: by
  rw [← measure_smul _ c]; rw [smul_set_sdiff]; rw [smul_smul]; rw [mul_inv_cancel]; rw [one_smul]

@[to_additive (attr := simp)]

中文:
定理 measure_sdiff_inv_smul
  条件: (c : G) (s t : 集合 α)
  结论: μ (s \ c⁻¹ • t) = μ (c • s \ t)
  证明: by
  rw [← measure_smul _ c]; rw [smul_set_sdiff]; rw [smul_smul]; rw [mul_inv_cancel]; rw [one_smul]

@[to_additive (attr := simp)]

Depends on / 依赖: measure_smul, mul_inv_cancel, one_smul, smul_set_sdiff, smul_smul
-/
theorem measure_sdiff_inv_smul (c : G) (s t : Set α) : μ (s \ c⁻¹ • t) = μ (c • s \ t) := by
  rw [← measure_smul _ c]; rw [smul_set_sdiff]; rw [smul_smul]; rw [mul_inv_cancel]; rw [one_smul]

@[to_additive (attr := simp)]
/--
theorem `measure_inv_smul_sdiff` / 定理 `measure_inv_smul_sdiff`

English:
theorem measure_inv_smul_sdiff
  given: (c : G) (s t : Set α)
  statement: μ (c⁻¹ • s \ t) = μ (s \ c • t)
  proof: by
  simpa [inv_inv] using (measure_sdiff_inv_smul _ c⁻¹ _ _).symm

@[to_additive (attr := simp)]

中文:
定理 measure_inv_smul_sdiff
  条件: (c : G) (s t : 集合 α)
  结论: μ (c⁻¹ • s \ t) = μ (s \ c • t)
  证明: by
  simpa [inv_inv] using (measure_sdiff_inv_smul _ c⁻¹ _ _).symm

@[to_additive (attr := simp)]

Depends on / 依赖: inv_inv, measure_sdiff_inv_smul
-/
theorem measure_inv_smul_sdiff (c : G) (s t : Set α) : μ (c⁻¹ • s \ t) = μ (s \ c • t) := by
  simpa [inv_inv] using (measure_sdiff_inv_smul _ c⁻¹ _ _).symm

@[to_additive (attr := simp)]
/--
theorem `measure_symmDiff_inv_smul` / 定理 `measure_symmDiff_inv_smul`

English:
theorem measure_symmDiff_inv_smul
  given: (c : G) (s t : Set α)
  statement: μ (s ∆ (c⁻¹ • t)) = μ ((c • s) ∆ t)
  proof: by
  rw [← measure_smul _ c]; rw [smul_set_symmDiff]; rw [smul_smul]; rw [mul_inv_cancel]; rw [one_smul]

@[to_additive (attr := simp)]

中文:
定理 measure_symmDiff_inv_smul
  条件: (c : G) (s t : 集合 α)
  结论: μ (s ∆ (c⁻¹ • t)) = μ ((c • s) ∆ t)
  证明: by
  rw [← measure_smul _ c]; rw [smul_set_symmDiff]; rw [smul_smul]; rw [mul_inv_cancel]; rw [one_smul]

@[to_additive (attr := simp)]

Depends on / 依赖: measure_smul, mul_inv_cancel, one_smul, smul_set_symmDiff, smul_smul
-/
theorem measure_symmDiff_inv_smul (c : G) (s t : Set α) : μ (s ∆ (c⁻¹ • t)) = μ ((c • s) ∆ t) := by
  rw [← measure_smul _ c]; rw [smul_set_symmDiff]; rw [smul_smul]; rw [mul_inv_cancel]; rw [one_smul]

@[to_additive (attr := simp)]
/--
theorem `measure_inv_smul_symmDiff` / 定理 `measure_inv_smul_symmDiff`

English:
theorem measure_inv_smul_symmDiff
  given: (c : G) (s t : Set α)
  statement: μ ((c⁻¹ • s) ∆ t) = μ (s ∆ (c • t))
  proof: by
  simpa [inv_inv] using (measure_symmDiff_inv_smul _ c⁻¹ _ _).symm

中文:
定理 measure_inv_smul_symmDiff
  条件: (c : G) (s t : 集合 α)
  结论: μ ((c⁻¹ • s) ∆ t) = μ (s ∆ (c • t))
  证明: by
  simpa [inv_inv] using (measure_symmDiff_inv_smul _ c⁻¹ _ _).symm

Depends on / 依赖: inv_inv, measure_symmDiff_inv_smul
-/
theorem measure_inv_smul_symmDiff (c : G) (s t : Set α) : μ ((c⁻¹ • s) ∆ t) = μ (s ∆ (c • t)) := by
  simpa [inv_inv] using (measure_symmDiff_inv_smul _ c⁻¹ _ _).symm

variable {μ}

@[to_additive]
/--
theorem `measure_smul_eq_zero_iff` / 定理 `measure_smul_eq_zero_iff`

English:
theorem measure_smul_eq_zero_iff
  given: {s} (c : G)
  statement: μ (c • s) = 0 ↔ μ s = 0
  proof: by
  rw [measure_smul]

@[to_additive]

中文:
定理 measure_smul_eq_zero_iff
  条件: {s} (c : G)
  结论: μ (c • s) = 0 ↔ μ s = 0
  证明: by
  rw [measure_smul]

@[to_additive]

Depends on / 依赖: measure_smul
-/
theorem measure_smul_eq_zero_iff {s} (c : G) : μ (c • s) = 0 ↔ μ s = 0 := by
  rw [measure_smul]

@[to_additive]
/--
theorem `measure_smul_null` / 定理 `measure_smul_null`

English:
theorem measure_smul_null
  given: {s} (h : μ s = 0) (c : G)
  statement: μ (c • s) = 0
  proof: (measure_smul_eq_zero_iff _).2 h

@[to_additive (attr := simp)]

中文:
定理 measure_smul_null
  条件: {s} (h : μ s = 0) (c : G)
  结论: μ (c • s) = 0
  证明: (measure_smul_eq_zero_iff _).2 h

@[to_additive (attr := simp)]

Depends on / 依赖: measure_smul_eq_zero_iff
-/
theorem measure_smul_null {s} (h : μ s = 0) (c : G) : μ (c • s) = 0 :=
  (measure_smul_eq_zero_iff _).2 h

@[to_additive (attr := simp)]
/--
theorem `smul_mem_ae` / 定理 `smul_mem_ae`

English:
theorem smul_mem_ae
  given: (c : G) {s : Set α}
  statement: c • s in ae μ ↔ s in ae μ
  proof: by
  simp only [mem_ae_iff, ← smul_set_compl, measure_smul_eq_zero_iff]

@[to_additive (attr := simp)]

中文:
定理 smul_mem_ae
  条件: (c : G) {s : 集合 α}
  结论: c • s in ae μ ↔ s in ae μ
  证明: by
  simp only [mem_ae_iff, ← smul_set_compl, measure_smul_eq_zero_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: measure_smul_eq_zero_iff, mem_ae_iff, smul_set_compl
-/
theorem smul_mem_ae (c : G) {s : Set α} : c • s in ae μ ↔ s in ae μ := by
  simp only [mem_ae_iff, ← smul_set_compl, measure_smul_eq_zero_iff]

@[to_additive (attr := simp)]
/--
theorem `smul_ae` / 定理 `smul_ae`

English:
theorem smul_ae
  given: (c : G)
  statement: c • ae μ = ae μ
  proof: by
  ext s
  simp only [mem_smul_filter, preimage_smul, smul_mem_ae]

@[to_additive (attr := simp)]

中文:
定理 smul_ae
  条件: (c : G)
  结论: c • ae μ = ae μ
  证明: by
  ext s
  simp only [mem_smul_filter, preimage_smul, smul_mem_ae]

@[to_additive (attr := simp)]

Depends on / 依赖: mem_smul_filter, preimage_smul, smul_mem_ae
-/
theorem smul_ae (c : G) : c • ae μ = ae μ := by
  ext s
  simp only [mem_smul_filter, preimage_smul, smul_mem_ae]

@[to_additive (attr := simp)]
/--
theorem `eventuallyConst_smul_set_ae` / 定理 `eventuallyConst_smul_set_ae`

English:
theorem eventuallyConst_smul_set_ae
  given: (c : G) {s : Set α}
  proof: by
  rw [← preimage_smul_inv]; rw [eventuallyConst_preimage]; rw [Filter.map_smul]; rw [smul_ae]

@[to_additive (attr := simp)]

中文:
定理 eventuallyConst_smul_set_ae
  条件: (c : G) {s : 集合 α}
  证明: by
  rw [← preimage_smul_inv]; rw [eventuallyConst_preimage]; rw [Filter.map_smul]; rw [smul_ae]

@[to_additive (attr := simp)]

Depends on / 依赖: Filter, Filter.map_smul, eventuallyConst_preimage, map_smul, preimage_smul_inv, smul_ae
-/
theorem eventuallyConst_smul_set_ae (c : G) {s : Set α} :
    EventuallyConst (c • s : Set α) (ae μ) ↔ EventuallyConst s (ae μ) := by
  rw [← preimage_smul_inv]; rw [eventuallyConst_preimage]; rw [Filter.map_smul]; rw [smul_ae]

@[to_additive (attr := simp)]
/--
theorem `smul_set_ae_le` / 定理 `smul_set_ae_le`

English:
theorem smul_set_ae_le
  given: (c : G) {s t : Set α}
  statement: c • s <=ᵐ[μ] c • t ↔ s <=ᵐ[μ] t
  proof: by
  simp only [ae_le_set, ← smul_set_sdiff, measure_smul_eq_zero_iff]

中文:
定理 smul_set_ae_le
  条件: (c : G) {s t : 集合 α}
  结论: c • s <=ᵐ[μ] c • t ↔ s <=ᵐ[μ] t
  证明: by
  simp only [ae_le_set, ← smul_set_sdiff, measure_smul_eq_zero_iff]

Depends on / 依赖: ae_le_set, measure_smul_eq_zero_iff, smul_set_sdiff
-/
theorem smul_set_ae_le (c : G) {s t : Set α} : c • s <=ᵐ[μ] c • t ↔ s <=ᵐ[μ] t := by
  simp only [ae_le_set, ← smul_set_sdiff, measure_smul_eq_zero_iff]

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
theorem `smul_set_ae_eq` / 定理 `smul_set_ae_eq`

English:
theorem smul_set_ae_eq
  given: (c : G) {s t : Set α}
  statement: c • s =ᵐ[μ] c • t ↔ s =ᵐ[μ] t
  proof: by
  simp only [Filter.eventuallyLE_antisymm_iff, smul_set_ae_le]

中文:
定理 smul_set_ae_eq
  条件: (c : G) {s t : 集合 α}
  结论: c • s =ᵐ[μ] c • t ↔ s =ᵐ[μ] t
  证明: by
  simp only [Filter.eventuallyLE_antisymm_iff, smul_set_ae_le]

Depends on / 依赖: Filter, Filter.eventuallyLE_antisymm_iff, eventuallyLE_antisymm_iff, smul_set_ae_le
-/
theorem smul_set_ae_eq (c : G) {s t : Set α} : c • s =ᵐ[μ] c • t ↔ s =ᵐ[μ] t := by
  simp only [Filter.eventuallyLE_antisymm_iff, smul_set_ae_le]

end AE

section MeasurableConstSMul

variable {m : MeasurableSpace α} [SMul M α] [MeasurableConstSMul M α] (c : M)
  (μ : Measure α) [SMulInvariantMeasure M α μ]

@[to_additive (attr := simp)]
/--
theorem `measurePreserving_smul` / 定理 `measurePreserving_smul`

English:
theorem measurePreserving_smul
  statement: MeasurePreserving (c • ·) μ μ
  proof: { measurable := measurable_const_smul c
    map_eq := by
      ext1 s hs
      rw [map_apply (measurable_const_smul c) hs]
      exact SMulInvariantMeasure.measure_preimage_smul c hs }

@[to_additive (attr := simp)]

中文:
定理 measurePreserving_smul
  结论: 保测 (c • ·) μ μ
  证明: { measurable := measurable_const_smul c
    map_eq := by
      ext1 s hs
      rw [map_apply (measurable_const_smul c) hs]
      exact SMulInvariantMeasure.measure_preimage_smul c hs }

@[to_additive (attr := simp)]

Depends on / 依赖: SMulInvariantMeasure, SMulInvariantMeasure.measure_preimage_smul, map_apply, map_eq, measurable, measurable_const_smul, measure_preimage_smul
-/
theorem measurePreserving_smul : MeasurePreserving (c • ·) μ μ :=
  { measurable := measurable_const_smul c
    map_eq := by
      ext1 s hs
      rw [map_apply (measurable_const_smul c) hs]
      exact SMulInvariantMeasure.measure_preimage_smul c hs }

@[to_additive (attr := simp)]
/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  statement: map (c • ·) μ = μ
  proof: (measurePreserving_smul c μ).map_eq

中文:
定理 map_smul
  结论: map (c • ·) μ = μ
  证明: (measurePreserving_smul c μ).map_eq
-/
protected theorem map_smul : map (c • ·) μ = μ :=
  (measurePreserving_smul c μ).map_eq

end MeasurableConstSMul

@[to_additive]
/--
theorem `MeasurePreserving.smulInvariantMeasure_iterateMulAct` / 定理 `MeasurePreserving.smulInvariantMeasure_iterateMulAct`

English:
theorem MeasurePreserving.smulInvariantMeasure_iterateMulAct
  proof: ⟨fun n _s hs => (hf.iterate n.val).measure_preimage hs.nullMeasurableSet⟩

@[to_additive]

中文:
定理 保测.smulInvariantMeasure_iterateMulAct
  证明: ⟨fun n _s hs => (hf.iterate n.val).measure_preimage hs.nullMeasurableSet⟩

@[to_additive]

Depends on / 依赖: hf.iterate, hs.nullMeasurableSet, iterate, measure_preimage, n.val, nullMeasurableSet
-/
theorem MeasurePreserving.smulInvariantMeasure_iterateMulAct
    {f : α -> α} {_ : MeasurableSpace α} {μ : Measure α} (hf : MeasurePreserving f μ μ) :
    SMulInvariantMeasure (IterateMulAct f) α μ :=
  ⟨fun n _s hs => (hf.iterate n.val).measure_preimage hs.nullMeasurableSet⟩

@[to_additive]
/--
theorem `smulInvariantMeasure_iterateMulAct` / 定理 `smulInvariantMeasure_iterateMulAct`

English:
theorem smulInvariantMeasure_iterateMulAct
  proof: ⟨fun _ =>
    have := hf.measurableSMul₂_iterateMulAct
    measurePreserving_smul (IterateMulAct.mk (f := f) 1) μ,
    MeasurePreserving.smulInvariantMeasure_iterateMulAct⟩

中文:
定理 smulInvariantMeasure_iterateMulAct
  证明: ⟨fun _ =>
    have := hf.measurableSMul₂_iterateMulAct
    measurePreserving_smul (IterateMulAct.mk (f := f) 1) μ,
    MeasurePreserving.smulInvariantMeasure_iterateMulAct⟩

Depends on / 依赖: IterateMulAct, IterateMulAct.mk, MeasurePreserving, MeasurePreserving.smulInvariantMeasure_iterateMulAct, hf.measurableSMul, measurePreserving_smul, smulInvariantMeasure_iterateMulAct
-/
theorem smulInvariantMeasure_iterateMulAct
    {f : α -> α} {_ : MeasurableSpace α} {μ : Measure α} (hf : Measurable f) :
    SMulInvariantMeasure (IterateMulAct f) α μ ↔ MeasurePreserving f μ μ :=
  ⟨fun _ =>
    have := hf.measurableSMul₂_iterateMulAct
    measurePreserving_smul (IterateMulAct.mk (f := f) 1) μ,
    MeasurePreserving.smulInvariantMeasure_iterateMulAct⟩

section SMulHomClass

universe uM uN uα uβ
variable {M : Type uM} {N : Type uN} {α : Type uα} {β : Type uβ}
  [MeasurableSpace α] [MeasurableSpace β]

@[to_additive]
/--
theorem `smulInvariantMeasure_map` / 定理 `smulInvariantMeasure_map`

English:
theorem smulInvariantMeasure_map
  statement: [SMul M α] [SMul M β]
  proof: calc
    map f μ ((m • ·) ⁻¹' S)
_ = μ (f ⁻¹' (m • ·) ⁻¹' S) := map_apply hf hS.preimage (measurable_const_smul _)
    _ = μ ((m • f ·) ⁻¹' S) := by rw [preimage_preimage]
    _ = μ ((f <| m • ·) ⁻¹' S) := by simp_rw [hsmul]
    _ = μ ((m • ·) ⁻¹' f ⁻¹' S) := by rw [← preimage_preimage]
    _ = μ (f ⁻¹' S) := by rw [SMulInvariantMeasure.measure_preimage_smul m (hS.preimage hf)]
    _ = map f μ S := (map_apply hf hS).symm

@[to_additive]

中文:
定理 smulInvariantMeasure_map
  结论: [标量乘法 M α] [标量乘法 M β]
  证明: calc
    map f μ ((m • ·) ⁻¹' S)
_ = μ (f ⁻¹' (m • ·) ⁻¹' S) := map_apply hf hS.preimage (measurable_const_smul _)
    _ = μ ((m • f ·) ⁻¹' S) := by rw [preimage_preimage]
    _ = μ ((f <| m • ·) ⁻¹' S) := by simp_rw [hsmul]
    _ = μ ((m • ·) ⁻¹' f ⁻¹' S) := by rw [← preimage_preimage]
    _ = μ (f ⁻¹' S) := by rw [SMulInvariantMeasure.measure_preimage_smul m (hS.preimage hf)]
    _ = map f μ S := (map_apply hf hS).symm

@[to_additive]
-/
theorem smulInvariantMeasure_map [SMul M α] [SMul M β]
    [MeasurableConstSMul M β]
    (μ : Measure α) [SMulInvariantMeasure M α μ] (f : α -> β)
    (hsmul : forall (m : M) a, f (m • a) = m • f a) (hf : Measurable f) :
    SMulInvariantMeasure M β (map f μ) where
  measure_preimage_smul m S hS := calc
    map f μ ((m • ·) ⁻¹' S)
_ = μ (f ⁻¹' (m • ·) ⁻¹' S) := map_apply hf hS.preimage (measurable_const_smul _)
    _ = μ ((m • f ·) ⁻¹' S) := by rw [preimage_preimage]
    _ = μ ((f <| m • ·) ⁻¹' S) := by simp_rw [hsmul]
    _ = μ ((m • ·) ⁻¹' f ⁻¹' S) := by rw [← preimage_preimage]
    _ = μ (f ⁻¹' S) := by rw [SMulInvariantMeasure.measure_preimage_smul m (hS.preimage hf)]
    _ = map f μ S := (map_apply hf hS).symm

@[to_additive]
/--
Instance `smulInvariantMeasure_map_smul` / 实例 `smulInvariantMeasure_map_smul`

English:
instance smulInvariantMeasure_map_smul
  signature: [SMul M α] [SMul N α] [SMulCommClass N M α]
  body: smulInvariantMeasure_map μ _ (smul_comm n) measurable_const_smul _

中文:
实例 smulInvariantMeasure_map_smul
  签名: [标量乘法 M α] [标量乘法 N α] [标量交换类 N M α]
  定义体: smulInvariantMeasure_map μ _ (smul_comm n) measurable_const_smul _

Depends on / 依赖: measurable_const_smul, smulInvariantMeasure_map, smul_comm
-/
instance smulInvariantMeasure_map_smul [SMul M α] [SMul N α] [SMulCommClass N M α]
    [MeasurableConstSMul M α] [MeasurableConstSMul N α]
    (μ : Measure α) [SMulInvariantMeasure M α μ] (n : N) :
    SMulInvariantMeasure M α (map (n • ·) μ) :=
smulInvariantMeasure_map μ _ (smul_comm n) measurable_const_smul _

end SMulHomClass

variable (G) {m : MeasurableSpace α} [Group G] [MulAction G α] (μ : Measure α)

variable [MeasurableConstSMul G α] in
/-- Equivalent definitions of a measure invariant under a multiplicative action of a group.

0. `SMulInvariantMeasure G α μ`;

1. for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under scalar
  multiplication by `c` is equal to the measure of `s`;

2. for every `c : G` and a measurable set `s`, the measure of the image `c • s` of `s` under
  scalar multiplication by `c` is equal to the measure of `s`;

3. property 1 for any set, including non-measurable ones;
4. property 2 for any set, including non-measurable ones;

5. for any `c : G`, scalar multiplication by `c` maps `μ` to `μ`;

6. for any `c : G`, scalar multiplication by `c` is a measure-preserving map. -/
@[to_additive]
/--
theorem `smulInvariantMeasure_tfae` / 定理 `smulInvariantMeasure_tfae`

English:
theorem smulInvariantMeasure_tfae
  proof: by
  tfae_have 1 ↔ 2 := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  tfae_have 1 -> 6 := fun h c => (measurePreserving_smul c μ).map_eq
  tfae_have 6 -> 7 := fun H c => ⟨measurable_const_smul c, H c⟩
  tfae_have 7 -> 4 := fun H c => (H c).measure_preimage_emb (measurableEmbedding_const_smul c)
  tfae_have 4 -> 5
  | H, c, s => by
    rw [← preimage_smul_inv]
    apply H
  tfae_have 5 -> 3 := fun H c s _ => H c s
  tfae_have 3 -> 2
  | H, c, s, hs => by
    rw [preimage_smul]
    exact H c⁻¹ s hs
  tfae_finish

中文:
定理 smulInvariantMeasure_tfae
  证明: by
  tfae_have 1 ↔ 2 := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  tfae_have 1 -> 6 := fun h c => (measurePreserving_smul c μ).map_eq
  tfae_have 6 -> 7 := fun H c => ⟨measurable_const_smul c, H c⟩
  tfae_have 7 -> 4 := fun H c => (H c).measure_preimage_emb (measurableEmbedding_const_smul c)
  tfae_have 4 -> 5
  | H, c, s => by
    rw [← preimage_smul_inv]
    apply H
  tfae_have 5 -> 3 := fun H c s _ => H c s
  tfae_have 3 -> 2
  | H, c, s, hs => by
    rw [preimage_smul]
    exact H c⁻¹ s hs
  tfae_finish

Depends on / 依赖: map_eq, measurableEmbedding_const_smul, measurable_const_smul, measurePreserving_smul, measure_preimage_emb, preimage_smul, preimage_smul_inv, tfae_finish, tfae_have
-/
theorem smulInvariantMeasure_tfae :
    List.TFAE
      [SMulInvariantMeasure G α μ,
        forall (c : G) (s), MeasurableSet s -> μ ((c • ·) ⁻¹' s) = μ s,
        forall (c : G) (s), MeasurableSet s -> μ (c • s) = μ s,
        forall (c : G) (s), μ ((c • ·) ⁻¹' s) = μ s,
        forall (c : G) (s), μ (c • s) = μ s,
        forall c : G, Measure.map (c • ·) μ = μ,
        forall c : G, MeasurePreserving (c • ·) μ μ] := by
  tfae_have 1 ↔ 2 := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  tfae_have 1 -> 6 := fun h c => (measurePreserving_smul c μ).map_eq
  tfae_have 6 -> 7 := fun H c => ⟨measurable_const_smul c, H c⟩
  tfae_have 7 -> 4 := fun H c => (H c).measure_preimage_emb (measurableEmbedding_const_smul c)
  tfae_have 4 -> 5
  | H, c, s => by
    rw [← preimage_smul_inv]
    apply H
  tfae_have 5 -> 3 := fun H c s _ => H c s
  tfae_have 3 -> 2
  | H, c, s, hs => by
    rw [preimage_smul]
    exact H c⁻¹ s hs
  tfae_finish

/-- Equivalent definitions of a measure invariant under an additive action of a group.

- 0: `VAddInvariantMeasure G α μ`;

- 1: for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under
     vector addition `(c +ᵥ ·)` is equal to the measure of `s`;

- 2: for every `c : G` and a measurable set `s`, the measure of the image `c +ᵥ s` of `s` under
     vector addition `(c +ᵥ ·)` is equal to the measure of `s`;

- 3, 4: properties 2, 3 for any set, including non-measurable ones;

- 5: for any `c : G`, vector addition of `c` maps `μ` to `μ`;

- 6: for any `c : G`, vector addition of `c` is a measure-preserving map. -/
add_decl_doc vaddInvariantMeasure_tfae

variable {G}
variable [SMulInvariantMeasure G α μ]

variable {μ}
variable [MeasurableConstSMul G α] in
@[to_additive]
/--
theorem `NullMeasurableSet.smul` / 定理 `NullMeasurableSet.smul`

English:
theorem NullMeasurableSet.smul
  given: {s} (hs : NullMeasurableSet s μ) (c : G)
  proof: by
  simpa only [← preimage_smul_inv] using
    hs.preimage (measurePreserving_smul _ _).quasiMeasurePreserving

中文:
定理 NullMeasurableSet.smul
  条件: {s} (hs : NullMeasurableSet s μ) (c : G)
  证明: by
  simpa only [← preimage_smul_inv] using
    hs.preimage (measurePreserving_smul _ _).quasiMeasurePreserving

Depends on / 依赖: hs.preimage, measurePreserving_smul, preimage, preimage_smul_inv, quasiMeasurePreserving
-/
theorem NullMeasurableSet.smul {s} (hs : NullMeasurableSet s μ) (c : G) :
    NullMeasurableSet (c • s) μ := by
  simpa only [← preimage_smul_inv] using
    hs.preimage (measurePreserving_smul _ _).quasiMeasurePreserving

section IsMinimal

variable (G)
variable [TopologicalSpace α] [ContinuousConstSMul G α] [MulAction.IsMinimal G α] {K U : Set α}

include G in
/-- If measure `μ` is invariant under a group action and is nonzero on a compact set `K`, then it is
positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0` instead of
`μ K ≠ 0`, see `MeasureTheory.measure_isOpen_pos_of_smulInvariant_of_ne_zero`. -/
@[to_additive]
/--
theorem `measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero` / 定理 `measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero`

English:
theorem measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero
  statement: (hK : IsCompact K) (hμK : μ K != 0)
  proof: let ⟨t, ht⟩ := hK.exists_finite_cover_smul G hU hne
  pos_iff_ne_zero.2 fun hμU =>
hμK
measure_mono_null ht
        (measure_biUnion_null_iff t.countable_toSet).2 fun _ _ => by rwa [measure_smul]

中文:
定理 measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero
  结论: (hK : 是紧集 K) (hμK : μ K != 0)
  证明: let ⟨t, ht⟩ := hK.exists_finite_cover_smul G hU hne
  pos_iff_ne_zero.2 fun hμU =>
hμK
measure_mono_null ht
        (measure_biUnion_null_iff t.countable_toSet).2 fun _ _ => by rwa [measure_smul]

Depends on / 依赖: countable_toSet, exists_finite_cover_smul, hK.exists_finite_cover_smul, measure_biUnion_null_iff, measure_mono_null, measure_smul, pos_iff_ne_zero, t.countable_toSet
-/
theorem measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero (hK : IsCompact K) (hμK : μ K != 0)
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U :=
  let ⟨t, ht⟩ := hK.exists_finite_cover_smul G hU hne
  pos_iff_ne_zero.2 fun hμU =>
hμK
measure_mono_null ht
        (measure_biUnion_null_iff t.countable_toSet).2 fun _ _ => by rwa [measure_smul]

/-- If measure `μ` is invariant under an additive group action and is nonzero on a compact set `K`,
then it is positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0`
instead of `μ K ≠ 0`, see `MeasureTheory.measure_isOpen_pos_of_vaddInvariant_of_ne_zero`. -/
add_decl_doc measure_isOpen_pos_of_vaddInvariant_of_compact_ne_zero

include G

@[to_additive]
/--
theorem `isLocallyFiniteMeasure_of_smulInvariant` / 定理 `isLocallyFiniteMeasure_of_smulInvariant`

English:
theorem isLocallyFiniteMeasure_of_smulInvariant
  given: (hU : IsOpen U) (hne : U.Nonempty) (hμU : μ U != ∞)
  proof: ⟨fun x =>
    let ⟨g, hg⟩ := hU.exists_smul_mem G x hne
    ⟨(g • ·) ⁻¹' U, (hU.preimage (continuous_id.const_smul _)).mem_nhds hg,
Ne.lt_top by rwa [measure_preimage_smul]⟩⟩

中文:
定理 isLocallyFiniteMeasure_of_smulInvariant
  条件: (hU : 是开集 U) (hne : U.非空) (hμU : μ U != ∞)
  证明: ⟨fun x =>
    let ⟨g, hg⟩ := hU.exists_smul_mem G x hne
    ⟨(g • ·) ⁻¹' U, (hU.preimage (continuous_id.const_smul _)).mem_nhds hg,
Ne.lt_top by rwa [measure_preimage_smul]⟩⟩

Depends on / 依赖: Ne.lt_top, const_smul, continuous_id, continuous_id.const_smul, exists_smul_mem, hU.exists_smul_mem, hU.preimage, lt_top, measure_preimage_smul, mem_nhds, preimage
-/
theorem isLocallyFiniteMeasure_of_smulInvariant (hU : IsOpen U) (hne : U.Nonempty) (hμU : μ U != ∞) :
    IsLocallyFiniteMeasure μ :=
  ⟨fun x =>
    let ⟨g, hg⟩ := hU.exists_smul_mem G x hne
    ⟨(g • ·) ⁻¹' U, (hU.preimage (continuous_id.const_smul _)).mem_nhds hg,
Ne.lt_top by rwa [measure_preimage_smul]⟩⟩

variable [Measure.Regular μ]

@[to_additive]
/--
theorem `measure_isOpen_pos_of_smulInvariant_of_ne_zero` / 定理 `measure_isOpen_pos_of_smulInvariant_of_ne_zero`

English:
theorem measure_isOpen_pos_of_smulInvariant_of_ne_zero
  statement: (hμ : μ != 0) (hU : IsOpen U)
  proof: let ⟨_K, hK, hμK⟩ := Regular.exists_isCompact_not_null.mpr hμ
  measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero G hK hμK hU hne

@[to_additive]

中文:
定理 measure_isOpen_pos_of_smulInvariant_of_ne_zero
  结论: (hμ : μ != 0) (hU : 是开集 U)
  证明: let ⟨_K, hK, hμK⟩ := Regular.exists_isCompact_not_null.mpr hμ
  measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero G hK hμK hU hne

@[to_additive]

Depends on / 依赖: Regular, Regular.exists_isCompact_not_null.mpr, exists_isCompact_not_null, measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero
-/
theorem measure_isOpen_pos_of_smulInvariant_of_ne_zero (hμ : μ != 0) (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < μ U :=
  let ⟨_K, hK, hμK⟩ := Regular.exists_isCompact_not_null.mpr hμ
  measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero G hK hμK hU hne

@[to_additive]
/--
theorem `measure_pos_iff_nonempty_of_smulInvariant` / 定理 `measure_pos_iff_nonempty_of_smulInvariant`

English:
theorem measure_pos_iff_nonempty_of_smulInvariant
  given: (hμ : μ != 0) (hU : IsOpen U)
  proof: ⟨fun h => nonempty_of_measure_ne_zero h.ne',
    measure_isOpen_pos_of_smulInvariant_of_ne_zero G hμ hU⟩

@[to_additive]

中文:
定理 measure_pos_iff_nonempty_of_smulInvariant
  条件: (hμ : μ != 0) (hU : 是开集 U)
  证明: ⟨fun h => nonempty_of_measure_ne_zero h.ne',
    measure_isOpen_pos_of_smulInvariant_of_ne_zero G hμ hU⟩

@[to_additive]

Depends on / 依赖: h.ne, measure_isOpen_pos_of_smulInvariant_of_ne_zero, nonempty_of_measure_ne_zero
-/
theorem measure_pos_iff_nonempty_of_smulInvariant (hμ : μ != 0) (hU : IsOpen U) :
    0 < μ U ↔ U.Nonempty :=
  ⟨fun h => nonempty_of_measure_ne_zero h.ne',
    measure_isOpen_pos_of_smulInvariant_of_ne_zero G hμ hU⟩

@[to_additive]
/--
theorem `measure_eq_zero_iff_eq_empty_of_smulInvariant` / 定理 `measure_eq_zero_iff_eq_empty_of_smulInvariant`

English:
theorem measure_eq_zero_iff_eq_empty_of_smulInvariant
  given: (hμ : μ != 0) (hU : IsOpen U)
  proof: by
  rw [← not_iff_not]; rw [← Ne]; rw [← pos_iff_ne_zero]; rw [measure_pos_iff_nonempty_of_smulInvariant G hμ hU]; rw [nonempty_iff_ne_empty]

中文:
定理 measure_eq_zero_iff_eq_empty_of_smulInvariant
  条件: (hμ : μ != 0) (hU : 是开集 U)
  证明: by
  rw [← not_iff_not]; rw [← Ne]; rw [← pos_iff_ne_zero]; rw [measure_pos_iff_nonempty_of_smulInvariant G hμ hU]; rw [nonempty_iff_ne_empty]

Depends on / 依赖: measure_pos_iff_nonempty_of_smulInvariant, nonempty_iff_ne_empty, not_iff_not, pos_iff_ne_zero
-/
theorem measure_eq_zero_iff_eq_empty_of_smulInvariant (hμ : μ != 0) (hU : IsOpen U) :
    μ U = 0 ↔ U = ∅ := by
  rw [← not_iff_not]; rw [← Ne]; rw [← pos_iff_ne_zero]; rw [measure_pos_iff_nonempty_of_smulInvariant G hμ hU]; rw [nonempty_iff_ne_empty]

end IsMinimal

end MeasureTheory
