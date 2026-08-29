/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Finitely strongly measurable functions in `Lp`

Functions in `Lp` for `0 < p < ∞` are finitely strongly measurable.

## Main statements

* `MemLp.aefinStronglyMeasurable`: if `MemLp f p μ` with `0 < p < ∞`, then
  `AEFinStronglyMeasurable f μ`.
* `Lp.finStronglyMeasurable`: for `0 < p < ∞`, `Lp` functions are finitely strongly measurable.

## References

* [Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.][Hytonen_VanNeerven_Veraar_Wies_2016]

-/

public section


open MeasureTheory Filter TopologicalSpace Function

open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

local infixr:25 " ->ₛ " => SimpleFunc

variable {α G : Type*} {p : Real>=0∞} {m m0 : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup G]
  {f : α -> G}

/--
theorem `MemLp.finStronglyMeasurable_of_stronglyMeasurable` / 定理 `MemLp.finStronglyMeasurable_of_stronglyMeasurable`

English:
theorem MemLp.finStronglyMeasurable_of_stronglyMeasurable
  statement: (hf : MemLp f p μ)
  proof: by
  borelize G
  have : SeparableSpace (Set.range f union {0} : Set G) :=
    hf_meas.separableSpace_range_union_singleton
  let fs := SimpleFunc.approxOn f hf_meas.measurable (Set.range f union {0}) 0 (by simp)
  refine ⟨fs, ?_, ?_⟩
  · have h_fs_Lp : forall n, MemLp (fs n) p μ :=
      SimpleFunc.memLp_approxOn_range hf_meas.measurable hf
    exact fun n => (fs n).measure_support_lt_top_of_memLp (h_fs_Lp n) hp_ne_zero hp_ne_top
  · intro x
    apply SimpleFunc.tendsto_approxOn
    apply subset_closure
    simp

中文:
定理 MemLp.finStronglyMeasurable_of_stronglyMeasurable
  结论: (hf : MemLp f p μ)
  证明: by
  borelize G
  have : SeparableSpace (Set.range f union {0} : Set G) :=
    hf_meas.separableSpace_range_union_singleton
  let fs := SimpleFunc.approxOn f hf_meas.measurable (Set.range f union {0}) 0 (by simp)
  refine ⟨fs, ?_, ?_⟩
  · have h_fs_Lp : forall n, MemLp (fs n) p μ :=
      SimpleFunc.memLp_approxOn_range hf_meas.measurable hf
    exact fun n => (fs n).measure_support_lt_top_of_memLp (h_fs_Lp n) hp_ne_zero hp_ne_top
  · intro x
    apply SimpleFunc.tendsto_approxOn
    apply subset_closure
    simp

Depends on / 依赖: SeparableSpace, Set.range, SimpleFunc, SimpleFunc.approxOn, SimpleFunc.memLp_approxOn_range, SimpleFunc.tendsto_approxOn, approxOn, borelize, h_fs_Lp, hf_meas, hf_meas.measurable, hf_meas.separableSpace_range_union_singleton, hp_ne_top, hp_ne_zero, measurable, measure_support_lt_top_of_memLp, memLp_approxOn_range, separableSpace_range_union_singleton, subset_closure, tendsto_approxOn
-/
theorem MemLp.finStronglyMeasurable_of_stronglyMeasurable (hf : MemLp f p μ)
    (hf_meas : StronglyMeasurable f) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) :
    FinStronglyMeasurable f μ := by
  borelize G
  have : SeparableSpace (Set.range f union {0} : Set G) :=
    hf_meas.separableSpace_range_union_singleton
  let fs := SimpleFunc.approxOn f hf_meas.measurable (Set.range f union {0}) 0 (by simp)
  refine ⟨fs, ?_, ?_⟩
  · have h_fs_Lp : forall n, MemLp (fs n) p μ :=
      SimpleFunc.memLp_approxOn_range hf_meas.measurable hf
    exact fun n => (fs n).measure_support_lt_top_of_memLp (h_fs_Lp n) hp_ne_zero hp_ne_top
  · intro x
    apply SimpleFunc.tendsto_approxOn
    apply subset_closure
    simp

/--
theorem `MemLp.aefinStronglyMeasurable` / 定理 `MemLp.aefinStronglyMeasurable`

English:
theorem MemLp.aefinStronglyMeasurable
  given: (hf : MemLp f p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  proof: ⟨hf.aestronglyMeasurable.mk f,
    ((memLp_congr_ae hf.aestronglyMeasurable.ae_eq_mk).mp
          hf).finStronglyMeasurable_of_stronglyMeasurable
      hf.aestronglyMeasurable.stronglyMeasurable_mk hp_ne_zero hp_ne_top,
    hf.aestronglyMeasurable.ae_eq_mk⟩

中文:
定理 MemLp.aefinStronglyMeasurable
  条件: (hf : MemLp f p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  证明: ⟨hf.aestronglyMeasurable.mk f,
    ((memLp_congr_ae hf.aestronglyMeasurable.ae_eq_mk).mp
          hf).finStronglyMeasurable_of_stronglyMeasurable
      hf.aestronglyMeasurable.stronglyMeasurable_mk hp_ne_zero hp_ne_top,
    hf.aestronglyMeasurable.ae_eq_mk⟩

Depends on / 依赖: ae_eq_mk, aestronglyMeasurable, finStronglyMeasurable_of_stronglyMeasurable, hf.aestronglyMeasurable.ae_eq_mk, hf.aestronglyMeasurable.mk, hf.aestronglyMeasurable.stronglyMeasurable_mk, hp_ne_top, hp_ne_zero, memLp_congr_ae, stronglyMeasurable_mk
-/
theorem MemLp.aefinStronglyMeasurable (hf : MemLp f p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) :
    AEFinStronglyMeasurable f μ :=
  ⟨hf.aestronglyMeasurable.mk f,
    ((memLp_congr_ae hf.aestronglyMeasurable.ae_eq_mk).mp
          hf).finStronglyMeasurable_of_stronglyMeasurable
      hf.aestronglyMeasurable.stronglyMeasurable_mk hp_ne_zero hp_ne_top,
    hf.aestronglyMeasurable.ae_eq_mk⟩

/--
theorem `Integrable.aefinStronglyMeasurable` / 定理 `Integrable.aefinStronglyMeasurable`

English:
theorem Integrable.aefinStronglyMeasurable
  given: (hf : Integrable f μ)
  statement: AEFinStronglyMeasurable f μ
  proof: (memLp_one_iff_integrable.mpr hf).aefinStronglyMeasurable one_ne_zero ENNReal.coe_ne_top

中文:
定理 可积.aefinStronglyMeasurable
  条件: (hf : 可积 f μ)
  结论: AEFinStronglyMeasurable f μ
  证明: (memLp_one_iff_integrable.mpr hf).aefinStronglyMeasurable one_ne_zero ENNReal.coe_ne_top

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, aefinStronglyMeasurable, coe_ne_top, memLp_one_iff_integrable, memLp_one_iff_integrable.mpr, one_ne_zero
-/
theorem Integrable.aefinStronglyMeasurable (hf : Integrable f μ) : AEFinStronglyMeasurable f μ :=
  (memLp_one_iff_integrable.mpr hf).aefinStronglyMeasurable one_ne_zero ENNReal.coe_ne_top

/--
theorem `Lp.finStronglyMeasurable` / 定理 `Lp.finStronglyMeasurable`

English:
theorem Lp.finStronglyMeasurable
  given: (f : Lp G p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  proof: (Lp.memLp f).finStronglyMeasurable_of_stronglyMeasurable (Lp.stronglyMeasurable f) hp_ne_zero
    hp_ne_top

中文:
定理 Lp.finStronglyMeasurable
  条件: (f : Lp G p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  证明: (Lp.memLp f).finStronglyMeasurable_of_stronglyMeasurable (Lp.stronglyMeasurable f) hp_ne_zero
    hp_ne_top

Depends on / 依赖: Lp.memLp, Lp.stronglyMeasurable, finStronglyMeasurable_of_stronglyMeasurable, hp_ne_top, hp_ne_zero, stronglyMeasurable
-/
theorem Lp.finStronglyMeasurable (f : Lp G p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) :
    FinStronglyMeasurable f μ :=
  (Lp.memLp f).finStronglyMeasurable_of_stronglyMeasurable (Lp.stronglyMeasurable f) hp_ne_zero
    hp_ne_top

end MeasureTheory
