/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureComp

import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.Deriv
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym

/-!
# Data processing inequality for the Kullback-Leibler divergence

The data processing inequality is a way to express the intuition that applying a (possibly random)
transformation to random variables cannot increase the information they contain.

## Main statements

We prove three versions of the data processing inequality for the Kullback-Leibler divergence, for
measurable maps, restrictions to sub-sigma-algebras, and composition with Markov kernels.
Let `μ, ν` be finite measures on `𝓧`, with sigma-algebra `m𝓧`.

* `klDiv_map_le`: `klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν` for a measurable function `g`.
* `klDiv_trim_le`: `klDiv (μ.trim hm) (ν.trim hm) ≤ klDiv μ ν` for a sub-sigma-algebra `m` of `m𝓧`
  (with `hm : m ≤ m𝓧`).
* `klDiv_comp_right_le`: `klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ klDiv μ ν` for a Markov kernel `κ`.

-/

public section

open Real MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace ConvexOn

variable {𝓧 𝓨 : Type*} {m m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : Real -> Real} {g : 𝓧 -> 𝓨}

/--
lemma `map_condExp_rnDeriv_le` / 引理 `map_condExp_rnDeriv_le`

English:
lemma map_condExp_rnDeriv_le
  statement: (hm : m <= m𝓧) (hf : StronglyMeasurable f)
  proof: hf_cvx.map_condExp_le_trim hm (hf_cvx.continuousOn_Ici hf_cont_at).lowerSemicontinuousOn hf
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg) isClosed_Ici Measure.integrable_toReal_rnDeriv h_int

中文:
引理 map_condExp_rnDeriv_le
  结论: (hm : m <= m𝓧) (hf : StronglyMeasurable f)
  证明: hf_cvx.map_condExp_le_trim hm (hf_cvx.continuousOn_Ici hf_cont_at).lowerSemicontinuousOn hf
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg) isClosed_Ici Measure.integrable_toReal_rnDeriv h_int

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, Measure, Measure.integrable_toReal_rnDeriv, ae_of_all, continuousOn_Ici, h_int, hf_cont_at, hf_cvx, hf_cvx.continuousOn_Ici, hf_cvx.map_condExp_le_trim, integrable_toReal_rnDeriv, isClosed_Ici, lowerSemicontinuousOn, map_condExp_le_trim, toReal_nonneg
-/
lemma map_condExp_rnDeriv_le (hm : m <= m𝓧) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) :
    (fun x => f ((ν[fun x => (μ.rnDeriv ν x).toReal | m]) x)) <=ᵐ[ν.trim hm]
      ν[fun x => f (μ.rnDeriv ν x).toReal | m] :=
  hf_cvx.map_condExp_le_trim hm (hf_cvx.continuousOn_Ici hf_cont_at).lowerSemicontinuousOn hf
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg) isClosed_Ici Measure.integrable_toReal_rnDeriv h_int

/--
lemma `comp_rnDeriv_map_le` / 引理 `comp_rnDeriv_map_le`

English:
lemma comp_rnDeriv_map_le
  statement: (hμν : μ ≪ ν) (hg : Measurable g) (hf : StronglyMeasurable f)
  proof: by
  filter_upwards [toReal_rnDeriv_map hμν hg,
ae_of_ae_trim _ hf_cvx.map_condExp_rnDeriv_le hg.comap_le hf hf_cont_at h_int] with a ha1 ha2
  calc f ((μ.map g).rnDeriv (ν.map g) (g a)).toReal
      = f ((ν[fun x => (μ.rnDeriv ν x).toReal | m𝓨.comap g]) a) := by rw [ha1]
    _ <= (ν[fun x => f (μ.r

中文:
引理 comp_rnDeriv_map_le
  结论: (hμν : μ ≪ ν) (hg : Measurable g) (hf : StronglyMeasurable f)
  证明: by
  filter_upwards [toReal_rnDeriv_map hμν hg,
ae_of_ae_trim _ hf_cvx.map_condExp_rnDeriv_le hg.comap_le hf hf_cont_at h_int] with a ha1 ha2
  calc f ((μ.map g).rnDeriv (ν.map g) (g a)).toReal
      = f ((ν[fun x => (μ.rnDeriv ν x).toReal | m𝓨.comap g]) a) := by rw [ha1]
    _ <= (ν[fun x => f (μ.r

Depends on / 依赖: ae_of_ae_trim, comap_le, filter_upwards, h_int, hf_cont_at, hf_cvx, hf_cvx.map_condExp_rnDeriv_le, hg.comap_le, map_condExp_rnDeriv_le, rnDeriv, toReal, toReal_rnDeriv_map
-/
lemma comp_rnDeriv_map_le (hμν : μ ≪ ν) (hg : Measurable g) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) :
    (fun x => f ((μ.map g).rnDeriv (ν.map g) (g x)).toReal) <=ᵐ[ν]
      ν[fun x => f (μ.rnDeriv ν x).toReal | m𝓨.comap g] := by
  filter_upwards [toReal_rnDeriv_map hμν hg,
ae_of_ae_trim _ hf_cvx.map_condExp_rnDeriv_le hg.comap_le hf hf_cont_at h_int] with a ha1 ha2
  calc f ((μ.map g).rnDeriv (ν.map g) (g a)).toReal
      = f ((ν[fun x => (μ.rnDeriv ν x).toReal | m𝓨.comap g]) a) := by rw [ha1]
    _ <= (ν[fun x => f (μ.rnDeriv ν x).toReal | m𝓨.comap g]) a := ha2

/--
lemma `integrable_comp_rnDeriv_map` / 引理 `integrable_comp_rnDeriv_map`

English:
lemma integrable_comp_rnDeriv_map
  statement: (hμν : μ ≪ ν) (hg : Measurable g) (hf : StronglyMeasurable f)
  proof: by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  obtain ⟨c, c', h⟩ : exists c c', forall x, 0 <= x -> c * x + c' <= f x :=
    hf_cvx.exists_affine_le_real isClosed_Ici hf_cont.lowerSemicontinuousOn
  rw [integrable_map_measure (StronglyMeasurable.aestronglyMeasurab

中文:
引理 integrable_comp_rnDeriv_map
  结论: (hμν : μ ≪ ν) (hg : Measurable g) (hf : StronglyMeasurable f)
  证明: by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  obtain ⟨c, c', h⟩ : exists c c', forall x, 0 <= x -> c * x + c' <= f x :=
    hf_cvx.exists_affine_le_real isClosed_Ici hf_cont.lowerSemicontinuousOn
  rw [integrable_map_measure (StronglyMeasurable.aestronglyMeasurab

Depends on / 依赖: ContinuousOn, StronglyMeasurable, StronglyMeasurable.aestronglyMeasurable, aemeasurable, aestronglyMeasurable, continuousOn_Ici, exists_affine_le_real, fun_prop, hf_cont, hf_cont.lowerSemicontinuousOn, hf_cont_at, hf_cvx, hf_cvx.continuousOn_Ici, hf_cvx.exists_affine_le_real, hg.aemeasurable, integrable_map_measure, integrable_of_le_of_le, isClosed_Ici, lowerSemicontinuousOn, toReal
-/
lemma integrable_comp_rnDeriv_map (hμν : μ ≪ ν) (hg : Measurable g) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) :
    Integrable (fun x => f ((μ.map g).rnDeriv (ν.map g) x).toReal) (ν.map g) := by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  obtain ⟨c, c', h⟩ : exists c c', forall x, 0 <= x -> c * x + c' <= f x :=
    hf_cvx.exists_affine_le_real isClosed_Ici hf_cont.lowerSemicontinuousOn
  rw [integrable_map_measure (StronglyMeasurable.aestronglyMeasurable (by fun_prop))
      hg.aemeasurable]
  refine integrable_of_le_of_le (f := fun x => f ((∂μ.map g/∂ν.map g) (g x)).toReal)
    (g₁ := fun x => c * ((∂μ.map g/∂ν.map g) (g x)).toReal + c')
    (g₂ := fun x => (ν[fun x => f (μ.rnDeriv ν x).toReal | m𝓨.comap g]) x)
    ?_ ?_ ?_ ?_ integrable_condExp
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ (fun x => h _ ENNReal.toReal_nonneg)
  · exact hf_cvx.comp_rnDeriv_map_le hμν hg hf hf_cont_at h_int
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    rw [integrable_congr (toReal_rnDeriv_map hμν hg)]
    fun_prop

/--
lemma `comp_rnDeriv_trim_le` / 引理 `comp_rnDeriv_trim_le`

English:
lemma comp_rnDeriv_trim_le
  statement: (hm : m <= m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
  proof: by
  filter_upwards [toReal_rnDeriv_trim hm hμν,
    hf_cvx.map_condExp_rnDeriv_le hm hf hf_cont_at h_int] with a ha1 ha2
  calc f ((∂μ.trim hm/∂ν.trim hm) a).toReal
      = f ((ν[fun x => (μ.rnDeriv ν x).toReal | m]) a) := by rw [ha1]
    _ <= (ν[fun x => f (μ.rnDeriv ν x).toReal | m]) a := ha2

中文:
引理 comp_rnDeriv_trim_le
  结论: (hm : m <= m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
  证明: by
  filter_upwards [toReal_rnDeriv_trim hm hμν,
    hf_cvx.map_condExp_rnDeriv_le hm hf hf_cont_at h_int] with a ha1 ha2
  calc f ((∂μ.trim hm/∂ν.trim hm) a).toReal
      = f ((ν[fun x => (μ.rnDeriv ν x).toReal | m]) a) := by rw [ha1]
    _ <= (ν[fun x => f (μ.rnDeriv ν x).toReal | m]) a := ha2

Depends on / 依赖: filter_upwards, h_int, hf_cont_at, hf_cvx, hf_cvx.map_condExp_rnDeriv_le, map_condExp_rnDeriv_le, rnDeriv, toReal, toReal_rnDeriv_trim
-/
lemma comp_rnDeriv_trim_le (hm : m <= m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) :
    (fun x => f ((∂μ.trim hm/∂ν.trim hm) x).toReal) <=ᵐ[ν.trim hm]
      ν[fun x => f (μ.rnDeriv ν x).toReal | m] := by
  filter_upwards [toReal_rnDeriv_trim hm hμν,
    hf_cvx.map_condExp_rnDeriv_le hm hf hf_cont_at h_int] with a ha1 ha2
  calc f ((∂μ.trim hm/∂ν.trim hm) a).toReal
      = f ((ν[fun x => (μ.rnDeriv ν x).toReal | m]) a) := by rw [ha1]
    _ <= (ν[fun x => f (μ.rnDeriv ν x).toReal | m]) a := ha2

/--
lemma `integrable_comp_rnDeriv_trim` / 引理 `integrable_comp_rnDeriv_trim`

English:
lemma integrable_comp_rnDeriv_trim
  statement: (hm : m <= m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
  proof: by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  obtain ⟨c, c', h⟩ : exists c c', forall x, 0 <= x -> c * x + c' <= f x :=
    hf_cvx.exists_affine_le_real isClosed_Ici hf_cont.lowerSemicontinuousOn
  refine integrable_of_le_of_le (f := fun x => f ((∂μ.trim hm/∂ν.tr

中文:
引理 integrable_comp_rnDeriv_trim
  结论: (hm : m <= m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
  证明: by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  obtain ⟨c, c', h⟩ : exists c c', forall x, 0 <= x -> c * x + c' <= f x :=
    hf_cvx.exists_affine_le_real isClosed_Ici hf_cont.lowerSemicontinuousOn
  refine integrable_of_le_of_le (f := fun x => f ((∂μ.trim hm/∂ν.tr

Depends on / 依赖: ContinuousOn, StronglyMeasurable, StronglyMeasurable.aestronglyMeasurable, aestronglyMeasurable, continuousOn_Ici, exists_affine_le_real, hf_cont, hf_cont.lowerSemicontinuousOn, hf_cont_at, hf_cvx, hf_cvx.continuousOn_Ici, hf_cvx.exists_affine_le_real, integrable_of_le_of_le, isClosed_Ici, lowerSemicontinuousOn, rnDeriv, toReal
-/
lemma integrable_comp_rnDeriv_trim (hm : m <= m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) :
    Integrable (fun x => f ((μ.trim hm).rnDeriv (ν.trim hm) x).toReal) (ν.trim hm) := by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  obtain ⟨c, c', h⟩ : exists c c', forall x, 0 <= x -> c * x + c' <= f x :=
    hf_cvx.exists_affine_le_real isClosed_Ici hf_cont.lowerSemicontinuousOn
  refine integrable_of_le_of_le (f := fun x => f ((∂μ.trim hm/∂ν.trim hm) x).toReal)
    (g₁ := fun x => c * ((∂μ.trim hm/∂ν.trim hm) x).toReal + c')
    (g₂ := fun x => (ν[fun x => f (μ.rnDeriv ν x).toReal | m]) x)
    ?_ ?_ ?_ ?_ ?_
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ (fun x => h _ ENNReal.toReal_nonneg)
  · exact hf_cvx.comp_rnDeriv_trim_le hm hμν hf hf_cont_at h_int
  · exact (Integrable.const_mul (by fun_prop) _).add (integrable_const _)
  · exact integrable_condExp.trim hm stronglyMeasurable_condExp

/--
lemma `integrable_comp_condExp_rnDeriv` / 引理 `integrable_comp_condExp_rnDeriv`

English:
lemma integrable_comp_condExp_rnDeriv
  statement: (hm : m <= m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
  proof: by
  have h := integrable_comp_rnDeriv_trim hm hμν hf hf_cvx hf_cont_at h_int
  refine integrable_of_integrable_trim hm ((integrable_congr ?_).mp h)
  filter_upwards [toReal_rnDeriv_trim hm hμν] with a ha
  rw [ha]

中文:
引理 integrable_comp_condExp_rnDeriv
  结论: (hm : m <= m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
  证明: by
  have h := integrable_comp_rnDeriv_trim hm hμν hf hf_cvx hf_cont_at h_int
  refine integrable_of_integrable_trim hm ((integrable_congr ?_).mp h)
  filter_upwards [toReal_rnDeriv_trim hm hμν] with a ha
  rw [ha]

Depends on / 依赖: filter_upwards, h_int, hf_cont_at, hf_cvx, integrable_comp_rnDeriv_trim, integrable_congr, integrable_of_integrable_trim, toReal_rnDeriv_trim
-/
lemma integrable_comp_condExp_rnDeriv (hm : m <= m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) :
    Integrable (fun x => f ((ν[fun x => (μ.rnDeriv ν x).toReal | m]) x)) ν := by
  have h := integrable_comp_rnDeriv_trim hm hμν hf hf_cvx hf_cont_at h_int
  refine integrable_of_integrable_trim hm ((integrable_congr ?_).mp h)
  filter_upwards [toReal_rnDeriv_trim hm hμν] with a ha
  rw [ha]

end ConvexOn

namespace InformationTheory

variable {𝓧 𝓨 : Type*} {m m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {μ ν : Measure 𝓧}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν] {g : 𝓧 -> 𝓨}

/--
lemma `integrable_llr_map` / 引理 `integrable_llr_map`

English:
lemma integrable_llr_map
  statement: (hμν : μ ≪ ν) (hg : Measurable g)
  proof: by
  rw [← integrable_klFun_rnDeriv_iff (hμν.map hg)]
  refine convexOn_klFun.integrable_comp_rnDeriv_map hμν hg (by fun_prop) (by fun_prop) ?_
  rwa [integrable_klFun_rnDeriv_iff hμν]

中文:
引理 integrable_llr_map
  结论: (hμν : μ ≪ ν) (hg : Measurable g)
  证明: by
  rw [← integrable_klFun_rnDeriv_iff (hμν.map hg)]
  refine convexOn_klFun.integrable_comp_rnDeriv_map hμν hg (by fun_prop) (by fun_prop) ?_
  rwa [integrable_klFun_rnDeriv_iff hμν]

Depends on / 依赖: convexOn_klFun, convexOn_klFun.integrable_comp_rnDeriv_map, fun_prop, integrable_comp_rnDeriv_map, integrable_klFun_rnDeriv_iff
-/
lemma integrable_llr_map (hμν : μ ≪ ν) (hg : Measurable g)
    (h_int : Integrable (llr μ ν) μ) :
    Integrable (llr (μ.map g) (ν.map g)) (μ.map g) := by
  rw [← integrable_klFun_rnDeriv_iff (hμν.map hg)]
  refine convexOn_klFun.integrable_comp_rnDeriv_map hμν hg (by fun_prop) (by fun_prop) ?_
  rwa [integrable_klFun_rnDeriv_iff hμν]

/--
lemma `toReal_klDiv_map_of_ac` / 引理 `toReal_klDiv_map_of_ac`

English:
lemma toReal_klDiv_map_of_ac
  given: (hμν : μ ≪ ν) (hg : Measurable g)
  proof: by
  rw [toReal_klDiv_eq_integral_klFun (hμν.map hg)]; rw [integral_map hg.aemeasurable
      (StronglyMeasurable.aestronglyMeasurable (by fun_prop))]
  refine integral_congr_ae ?_
  filter_upwards [toReal_rnDeriv_map hμν hg] with a ha using by rw [ha]

中文:
引理 toReal_klDiv_map_of_ac
  条件: (hμν : μ ≪ ν) (hg : Measurable g)
  证明: by
  rw [toReal_klDiv_eq_integral_klFun (hμν.map hg)]; rw [integral_map hg.aemeasurable
      (StronglyMeasurable.aestronglyMeasurable (by fun_prop))]
  refine integral_congr_ae ?_
  filter_upwards [toReal_rnDeriv_map hμν hg] with a ha using by rw [ha]

Depends on / 依赖: StronglyMeasurable, StronglyMeasurable.aestronglyMeasurable, aemeasurable, aestronglyMeasurable, filter_upwards, fun_prop, hg.aemeasurable, integral_congr_ae, integral_map, toReal_klDiv_eq_integral_klFun, toReal_rnDeriv_map
-/
lemma toReal_klDiv_map_of_ac (hμν : μ ≪ ν) (hg : Measurable g) :
    (klDiv (μ.map g) (ν.map g)).toReal =
      ∫ x, klFun ((ν[fun x => (μ.rnDeriv ν x).toReal | m𝓨.comap g]) x) ∂ν := by
  rw [toReal_klDiv_eq_integral_klFun (hμν.map hg)]; rw [integral_map hg.aemeasurable
      (StronglyMeasurable.aestronglyMeasurable (by fun_prop))]
  refine integral_congr_ae ?_
  filter_upwards [toReal_rnDeriv_map hμν hg] with a ha using by rw [ha]

/--
lemma `klDiv_map_of_ac` / 引理 `klDiv_map_of_ac`

English:
lemma klDiv_map_of_ac
  given: (hμν : μ ≪ ν) (hg : Measurable g) (h_int : Integrable (llr μ ν) μ)
  proof: by
  rw [klDiv_eq_integral_klFun]; rw [if_pos ⟨hμν.map hg]; rw [integrable_llr_map hμν hg h_int⟩]
  congr
  rw [← toReal_klDiv_eq_integral_klFun (hμν.map hg)]; rw [toReal_klDiv_map_of_ac hμν hg]

中文:
引理 klDiv_map_of_ac
  条件: (hμν : μ ≪ ν) (hg : Measurable g) (h_int : 整数egrable (llr μ ν) μ)
  证明: by
  rw [klDiv_eq_integral_klFun]; rw [if_pos ⟨hμν.map hg]; rw [integrable_llr_map hμν hg h_int⟩]
  congr
  rw [← toReal_klDiv_eq_integral_klFun (hμν.map hg)]; rw [toReal_klDiv_map_of_ac hμν hg]

Depends on / 依赖: h_int, if_pos, integrable_llr_map, klDiv_eq_integral_klFun, toReal_klDiv_eq_integral_klFun, toReal_klDiv_map_of_ac
-/
lemma klDiv_map_of_ac (hμν : μ ≪ ν) (hg : Measurable g) (h_int : Integrable (llr μ ν) μ) :
    klDiv (μ.map g) (ν.map g) =
      ENNReal.ofReal (∫ x, klFun ((ν[fun x => (μ.rnDeriv ν x).toReal | m𝓨.comap g]) x) ∂ν) := by
  rw [klDiv_eq_integral_klFun]; rw [if_pos ⟨hμν.map hg]; rw [integrable_llr_map hμν hg h_int⟩]
  congr
  rw [← toReal_klDiv_eq_integral_klFun (hμν.map hg)]; rw [toReal_klDiv_map_of_ac hμν hg]

/--
lemma `toReal_klDiv_trim_of_ac` / 引理 `toReal_klDiv_trim_of_ac`

English:
lemma toReal_klDiv_trim_of_ac
  given: (hm : m <= m𝓧) (hμν : μ ≪ ν)
  proof: by
  simp [trim_eq_map, toReal_klDiv_map_of_ac hμν (measurable_id'' hm)]

中文:
引理 toReal_klDiv_trim_of_ac
  条件: (hm : m <= m𝓧) (hμν : μ ≪ ν)
  证明: by
  simp [trim_eq_map, toReal_klDiv_map_of_ac hμν (measurable_id'' hm)]

Depends on / 依赖: measurable_id, toReal_klDiv_map_of_ac, trim_eq_map
-/
lemma toReal_klDiv_trim_of_ac (hm : m <= m𝓧) (hμν : μ ≪ ν) :
    (klDiv (μ.trim hm) (ν.trim hm)).toReal =
      ∫ x, klFun ((ν[fun x => (μ.rnDeriv ν x).toReal | m]) x) ∂ν := by
  simp [trim_eq_map, toReal_klDiv_map_of_ac hμν (measurable_id'' hm)]

variable (μ ν) in
/--
theorem `klDiv_map_le` / 定理 `klDiv_map_le`

English:
theorem klDiv_map_le
  given: (hg : Measurable g)
  statement: klDiv (μ.map g) (ν.map g) <= klDiv μ ν
  proof: by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [klDiv_of_not_integrable h_int]
  rw [klDiv_map_of_ac hμν hg h_int]; rw [klDiv_eq_integral_klFun]
  simp only [hμν, h_int, and_self, ↓reduceIte]
  conv_rhs => rw [← integral_condExp hg.comap_le]
 

中文:
定理 klDiv_map_le
  条件: (hg : Measurable g)
  结论: klDiv (μ.map g) (ν.map g) <= klDiv μ ν
  证明: by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [klDiv_of_not_integrable h_int]
  rw [klDiv_map_of_ac hμν hg h_int]; rw [klDiv_eq_integral_klFun]
  simp only [hμν, h_int, and_self, ↓reduceIte]
  conv_rhs => rw [← integral_condExp hg.comap_le]
 

Depends on / 依赖: ContinuousWithinAt, Integrable, StronglyMeasurable, and_self, comap_le, conv_rhs, fun_prop, h_int, hf_cont, hg.comap_le, integrable_kl, integral_condExp, klDiv_eq_integral_klFun, klDiv_map_of_ac, klDiv_of_not_integrable, reduceIte, rnDeriv, toReal
-/
theorem klDiv_map_le (hg : Measurable g) : klDiv (μ.map g) (ν.map g) <= klDiv μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [klDiv_of_not_integrable h_int]
  rw [klDiv_map_of_ac hμν hg h_int]; rw [klDiv_eq_integral_klFun]
  simp only [hμν, h_int, and_self, ↓reduceIte]
  conv_rhs => rw [← integral_condExp hg.comap_le]
  gcongr 1
  have hf : StronglyMeasurable klFun := by fun_prop
  have hf_cont : ContinuousWithinAt klFun (Ici 0) 0 := by fun_prop
  have h_int' : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν := by
    rwa [integrable_klFun_rnDeriv_iff hμν]
  refine integral_mono_ae ?_ integrable_condExp ?_
  · exact convexOn_klFun.integrable_comp_condExp_rnDeriv hg.comap_le hμν hf hf_cont h_int'
  · refine ae_of_ae_trim hg.comap_le ?_
    exact convexOn_klFun.map_condExp_rnDeriv_le hg.comap_le hf hf_cont h_int'

variable (μ ν) in
/--
theorem `klDiv_trim_le` / 定理 `klDiv_trim_le`

English:
theorem klDiv_trim_le
  given: (hm : m <= m𝓧)
  statement: klDiv (μ.trim hm) (ν.trim hm) <= klDiv μ ν
  proof: by
  simp_rw [trim_eq_map]
  exact klDiv_map_le μ ν (measurable_id'' hm)

中文:
定理 klDiv_trim_le
  条件: (hm : m <= m𝓧)
  结论: klDiv (μ.trim hm) (ν.trim hm) <= klDiv μ ν
  证明: by
  simp_rw [trim_eq_map]
  exact klDiv_map_le μ ν (measurable_id'' hm)

Depends on / 依赖: klDiv_map_le, measurable_id, simp_rw, trim_eq_map
-/
theorem klDiv_trim_le (hm : m <= m𝓧) : klDiv (μ.trim hm) (ν.trim hm) <= klDiv μ ν := by
  simp_rw [trim_eq_map]
  exact klDiv_map_le μ ν (measurable_id'' hm)

variable (μ ν) in
/--
theorem `klDiv_comp_right_le` / 定理 `klDiv_comp_right_le`

English:
theorem klDiv_comp_right_le
  given: (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ]
  proof: calc klDiv (κ ∘ₘ μ) (κ ∘ₘ ν)
  _ <= klDiv (μ otimesₘ κ) (ν otimesₘ κ) := by
    rw [← Measure.snd_compProd]; rw [← Measure.snd_compProd]
    exact klDiv_map_le _ _ measurable_snd
  _ = klDiv μ ν := klDiv_compProd_left μ ν κ

中文:
定理 klDiv_comp_right_le
  条件: (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ]
  证明: calc klDiv (κ ∘ₘ μ) (κ ∘ₘ ν)
  _ <= klDiv (μ otimesₘ κ) (ν otimesₘ κ) := by
    rw [← Measure.snd_compProd]; rw [← Measure.snd_compProd]
    exact klDiv_map_le _ _ measurable_snd
  _ = klDiv μ ν := klDiv_compProd_left μ ν κ

Depends on / 依赖: Measure, Measure.snd_compProd, klDiv_compProd_left, klDiv_map_le, measurable_snd, snd_compProd
-/
theorem klDiv_comp_right_le (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) <= klDiv μ ν :=
  calc klDiv (κ ∘ₘ μ) (κ ∘ₘ ν)
  _ <= klDiv (μ otimesₘ κ) (ν otimesₘ κ) := by
    rw [← Measure.snd_compProd]; rw [← Measure.snd_compProd]
    exact klDiv_map_le _ _ measurable_snd
  _ = klDiv μ ν := klDiv_compProd_left μ ν κ

end InformationTheory
