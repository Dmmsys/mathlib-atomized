/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integration with respect to a finite product of measures

On a finite product of measure spaces, we show that a product of integrable functions each
depending on a single coordinate is integrable, in `MeasureTheory.integrable_fintype_prod`, and
that its integral is the product of the individual integrals,
in `MeasureTheory.integral_fintype_prod_eq_prod`.
-/

public section

open Fintype MeasureTheory MeasureTheory.Measure

namespace MeasureTheory

variable {𝕜 ι : Type*} [Fintype ι]

namespace Integrable

variable [NormedCommRing 𝕜]

/--
theorem `fin_nat_prod` / 定理 `fin_nat_prod`

English:
theorem fin_nat_prod
  statement: {n : Nat} {E : Fin n -> Type*}
  proof: by
  induction n with
  | zero => simp only [Finset.univ_eq_empty, Finset.prod_empty, isFiniteMeasure_iff,
      integrable_const_iff, pi_empty_univ, ENNReal.one_lt_top, or_true]
  | succ n n_ih =>
      have := ((measurePreserving_piFinSuccAbove μ 0).symm)
      rw [← this.integrable_comp_emb (Meas

中文:
定理 fin_nat_prod
  结论: {n : 自然数} {E : Fin n -> 类型}
  证明: by
  induction n with
  | zero => simp only [Finset.univ_eq_empty, Finset.prod_empty, isFiniteMeasure_iff,
      integrable_const_iff, pi_empty_univ, ENNReal.one_lt_top, or_true]
  | succ n n_ih =>
      have := ((measurePreserving_piFinSuccAbove μ 0).symm)
      rw [← this.integrable_comp_emb (Meas

Depends on / 依赖: ENNReal, ENNReal.one_lt_top, Fin.insertNthEquiv, Fin.insertNth_zero, Fin.prod_univ_succ, Fin.zero_succAbove, Finset, Finset.prod_empty, Finset.univ_eq_empty, Function, Function.comp_def, Integrable, MeasurableEquiv, MeasurableEquiv.measurableEmbedding, MeasurableEquiv.piFinSuccAbove_symm_apply, comp_def, insertNthEquiv, insertNth_zero, integrable_comp_emb, integrable_const_iff
-/
theorem fin_nat_prod {n : Nat} {E : Fin n -> Type*}
    {mE : forall i, MeasurableSpace (E i)} {μ : (i : Fin n) -> Measure (E i)} [forall i, SigmaFinite (μ i)]
    {f : (i : Fin n) -> E i -> 𝕜} (hf : forall i, Integrable (f i) (μ i)) :
    Integrable (fun (x : (i : Fin n) -> E i) => ∏ i, f i (x i)) (Measure.pi μ) := by
  induction n with
  | zero => simp only [Finset.univ_eq_empty, Finset.prod_empty, isFiniteMeasure_iff,
      integrable_const_iff, pi_empty_univ, ENNReal.one_lt_top, or_true]
  | succ n n_ih =>
      have := ((measurePreserving_piFinSuccAbove μ 0).symm)
      rw [← this.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero]
      simp only [Fin.zero_succAbove, Function.comp_def]
      have : Integrable (fun (x : (j : Fin n) -> E (Fin.succ j)) => ∏ j, f (Fin.succ j) (x j))
          (Measure.pi (fun i => μ i.succ)) :=
        n_ih (fun i => hf _)
      exact Integrable.mul_prod (hf 0) this

/--
theorem `fintype_prod_dep` / 定理 `fintype_prod_dep`

English:
theorem fintype_prod_dep
  statement: {E : ι -> Type*}
  proof: by
  let e := (equivFin ι).symm
  simp_rw [← (measurePreserving_piCongrLeft _ e).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _),
    ← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Function.comp_def,
    Equiv.piCongrLeft_apply_apply]
  exact .fin_nat_prod (fun i => hf _)

中文:
定理 fintype_prod_dep
  结论: {E : ι -> 类型}
  证明: by
  let e := (equivFin ι).symm
  simp_rw [← (measurePreserving_piCongrLeft _ e).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _),
    ← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Function.comp_def,
    Equiv.piCongrLeft_apply_apply]
  exact .fin_nat_prod (fun i => hf _)

Depends on / 依赖: Equiv.piCongrLeft_apply_apply, Function, Function.comp_def, MeasurableEquiv, MeasurableEquiv.coe_piCongrLeft, MeasurableEquiv.measurableEmbedding, coe_piCongrLeft, comp_def, e.prod_comp, equivFin, fin_nat_prod, integrable_comp_emb, measurableEmbedding, measurePreserving_piCongrLeft, piCongrLeft_apply_apply, prod_comp, simp_rw
-/
theorem fintype_prod_dep {E : ι -> Type*}
    {f : (i : ι) -> E i -> 𝕜} {mE : forall i, MeasurableSpace (E i)} {μ : (i : ι) -> Measure (E i)}
    [forall i, SigmaFinite (μ i)]
    (hf : forall i, Integrable (f i) (μ i)) :
    Integrable (fun (x : (i : ι) -> E i) => ∏ i, f i (x i)) (Measure.pi μ) := by
  let e := (equivFin ι).symm
  simp_rw [← (measurePreserving_piCongrLeft _ e).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _),
    ← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Function.comp_def,
    Equiv.piCongrLeft_apply_apply]
  exact .fin_nat_prod (fun i => hf _)

/--
theorem `fintype_prod` / 定理 `fintype_prod`

English:
theorem fintype_prod
  statement: {E : Type*}
  proof: Integrable.fintype_prod_dep hf

中文:
定理 fintype_prod
  结论: {E : 类型}
  证明: Integrable.fintype_prod_dep hf

Depends on / 依赖: Integrable, Integrable.fintype_prod_dep, fintype_prod_dep
-/
theorem fintype_prod {E : Type*}
    {f : ι -> E -> 𝕜} {mE : MeasurableSpace E} {μ : ι -> Measure E} [forall i, SigmaFinite (μ i)]
    (hf : forall i, Integrable (f i) (μ i)) :
    Integrable (fun (x : ι -> E) => ∏ i, f i (x i)) (Measure.pi μ) :=
  Integrable.fintype_prod_dep hf

end Integrable

variable [RCLike 𝕜]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `integral_fin_nat_prod_eq_prod` / 定理 `integral_fin_nat_prod_eq_prod`

English:
theorem integral_fin_nat_prod_eq_prod
  statement: {n : Nat} {E : Fin n -> Type*}
  proof: by
  induction n with
  | zero => simp [measureReal_def]
  | succ n n_ih =>
      calc
        _ = ∫ x : E 0 × ((i : Fin n) -> E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
          rw [← ((measurePreservi

中文:
定理 integral_fin_nat_prod_eq_prod
  结论: {n : 自然数} {E : Fin n -> 类型}
  证明: by
  induction n with
  | zero => simp [measureReal_def]
  | succ n n_ih =>
      calc
        _ = ∫ x : E 0 × ((i : Fin n) -> E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
          rw [← ((measurePreservi

Depends on / 依赖: Equiv.coe_fn_mk, Fin.cons_succ, Fin.cons_zero, Fin.insertNthEquiv, Fin.insertNth_zero, Fin.prod_univ_succ, Fin.succ, Fin.zero_succAbove, MeasurableEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply, Measure, Measure.pi, cast_eq, coe_fn_mk, cons_succ, cons_zero, i.succ, insertNthEquiv, insertNth_zero, integral_comp
-/
theorem integral_fin_nat_prod_eq_prod {n : Nat} {E : Fin n -> Type*}
    {mE : forall i, MeasurableSpace (E i)} {μ : (i : Fin n) -> Measure (E i)} [forall i, SigmaFinite (μ i)]
    (f : (i : Fin n) -> E i -> 𝕜) :
    ∫ x : (i : Fin n) -> E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp [measureReal_def]
  | succ n n_ih =>
      calc
        _ = ∫ x : E 0 × ((i : Fin n) -> E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).integral_comp']
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih]; rw [← integral_prod_mul]
        _ = ∏ i, ∫ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/--
theorem `integral_fin_nat_prod_volume_eq_prod` / 定理 `integral_fin_nat_prod_volume_eq_prod`

English:
theorem integral_fin_nat_prod_volume_eq_prod
  statement: {n : Nat} {E : Fin n -> Type*}
  proof: integral_fin_nat_prod_eq_prod _

中文:
定理 integral_fin_nat_prod_volume_eq_prod
  结论: {n : 自然数} {E : Fin n -> 类型}
  证明: integral_fin_nat_prod_eq_prod _

Depends on / 依赖: integral_fin_nat_prod_eq_prod
-/
theorem integral_fin_nat_prod_volume_eq_prod {n : Nat} {E : Fin n -> Type*}
    [forall i, MeasureSpace (E i)] [forall i, SigmaFinite (volume : Measure (E i))]
    (f : (i : Fin n) -> E i -> 𝕜) :
    ∫ x : (i : Fin n) -> E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x := integral_fin_nat_prod_eq_prod _

/--
theorem `integral_fintype_prod_eq_prod` / 定理 `integral_fintype_prod_eq_prod`

English:
theorem integral_fintype_prod_eq_prod
  statement: {E : ι -> Type*} (f : (i : ι) -> E i -> 𝕜)
  proof: by
  let e := (equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).integral_comp']
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
    MeasureTheory.integral_fin_nat_prod_eq_prod]

中文:
定理 integral_fintype_prod_eq_prod
  结论: {E : ι -> 类型} (f : (i : ι) -> E i -> 𝕜)
  证明: by
  let e := (equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).integral_comp']
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
    MeasureTheory.integral_fin_nat_prod_eq_prod]

Depends on / 依赖: Equiv.piCongrLeft_apply_apply, MeasurableEquiv, MeasurableEquiv.coe_piCongrLeft, MeasureTheory, MeasureTheory.integral_fin_nat_prod_eq_prod, coe_piCongrLeft, e.prod_comp, equivFin, integral_comp, integral_fin_nat_prod_eq_prod, measurePreserving_piCongrLeft, piCongrLeft_apply_apply, prod_comp, simp_rw
-/
theorem integral_fintype_prod_eq_prod {E : ι -> Type*} (f : (i : ι) -> E i -> 𝕜)
    {mE : forall i, MeasurableSpace (E i)} {μ : (i : ι) -> Measure (E i)} [forall i, SigmaFinite (μ i)] :
    ∫ x : (i : ι) -> E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫ x, f i x ∂(μ i) := by
  let e := (equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).integral_comp']
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
    MeasureTheory.integral_fin_nat_prod_eq_prod]

/--
theorem `integral_fintype_prod_volume_eq_prod` / 定理 `integral_fintype_prod_volume_eq_prod`

English:
theorem integral_fintype_prod_volume_eq_prod
  statement: {E : ι -> Type*} (f : (i : ι) -> E i -> 𝕜)
  proof: integral_fintype_prod_eq_prod _

中文:
定理 integral_fintype_prod_volume_eq_prod
  结论: {E : ι -> 类型} (f : (i : ι) -> E i -> 𝕜)
  证明: integral_fintype_prod_eq_prod _

Depends on / 依赖: integral_fintype_prod_eq_prod
-/
theorem integral_fintype_prod_volume_eq_prod {E : ι -> Type*} (f : (i : ι) -> E i -> 𝕜)
    [forall i, MeasureSpace (E i)] [forall i, SigmaFinite (volume : Measure (E i))] :
    ∫ x : (i : ι) -> E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x := integral_fintype_prod_eq_prod _

/--
theorem `integral_fintype_prod_eq_pow` / 定理 `integral_fintype_prod_eq_pow`

English:
theorem integral_fintype_prod_eq_pow
  statement: {E : Type*} (f : E -> 𝕜) {mE : MeasurableSpace E}
  proof: by
  rw [integral_fintype_prod_eq_prod]; rw [Finset.prod_const]; rw [card]

中文:
定理 integral_fintype_prod_eq_pow
  结论: {E : 类型} (f : E -> 𝕜) {mE : MeasurableSpace E}
  证明: by
  rw [integral_fintype_prod_eq_prod]; rw [Finset.prod_const]; rw [card]

Depends on / 依赖: Finset, Finset.prod_const, integral_fintype_prod_eq_prod, prod_const
-/
theorem integral_fintype_prod_eq_pow {E : Type*} (f : E -> 𝕜) {mE : MeasurableSpace E}
    {μ : Measure E} [SigmaFinite μ] :
    ∫ x : ι -> E, ∏ i, f (x i) ∂(Measure.pi (fun _ => μ)) = (∫ x, f x ∂μ) ^ (card ι) := by
  rw [integral_fintype_prod_eq_prod]; rw [Finset.prod_const]; rw [card]

/--
theorem `integral_fintype_prod_volume_eq_pow` / 定理 `integral_fintype_prod_volume_eq_pow`

English:
theorem integral_fintype_prod_volume_eq_pow
  statement: {E : Type*} (f : E -> 𝕜)
  proof: integral_fintype_prod_eq_pow _

中文:
定理 integral_fintype_prod_volume_eq_pow
  结论: {E : 类型} (f : E -> 𝕜)
  证明: integral_fintype_prod_eq_pow _

Depends on / 依赖: integral_fintype_prod_eq_pow
-/
theorem integral_fintype_prod_volume_eq_pow {E : Type*} (f : E -> 𝕜)
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    ∫ x : ι -> E, ∏ i, f (x i) = (∫ x, f x) ^ (card ι) := integral_fintype_prod_eq_pow _

variable {X : ι -> Type*} {mX : forall i, MeasurableSpace (X i)} {μ : (i : ι) -> Measure (X i)}
    {E : Type*} [NormedAddCommGroup E]

/--
lemma `integrable_comp_eval` / 引理 `integrable_comp_eval`

English:
lemma integrable_comp_eval
  statement: [forall i, IsFiniteMeasure (μ i)] {i : ι} {f : X i -> E}
  proof: by
  refine Integrable.comp_measurable ?_ (by fun_prop)
  classical
  rw [Measure.pi_map_eval]
exact hf.smul_measure ENNReal.prod_ne_top (by finiteness)

中文:
引理 integrable_comp_eval
  结论: [对任意 i, IsFiniteMeasure (μ i)] {i : ι} {f : X i -> E}
  证明: by
  refine Integrable.comp_measurable ?_ (by fun_prop)
  classical
  rw [Measure.pi_map_eval]
exact hf.smul_measure ENNReal.prod_ne_top (by finiteness)

Depends on / 依赖: ENNReal, ENNReal.prod_ne_top, Integrable, Integrable.comp_measurable, Measure, Measure.pi_map_eval, classical, comp_measurable, finiteness, fun_prop, hf.smul_measure, pi_map_eval, prod_ne_top, smul_measure
-/
lemma integrable_comp_eval [forall i, IsFiniteMeasure (μ i)] {i : ι} {f : X i -> E}
    (hf : Integrable f (μ i)) :
    Integrable (fun x => f (x i)) (Measure.pi μ) := by
  refine Integrable.comp_measurable ?_ (by fun_prop)
  classical
  rw [Measure.pi_map_eval]
exact hf.smul_measure ENNReal.prod_ne_top (by finiteness)

/--
lemma `integrable_eval` / 引理 `integrable_eval`

English:
lemma integrable_eval
  statement: [forall i, NormedAddCommGroup (X i)] [forall i, IsFiniteMeasure (μ i)] {i : ι}
  proof: integrable_comp_eval h

中文:
引理 integrable_eval
  结论: [对任意 i, NormedAddCommGroup (X i)] [对任意 i, IsFiniteMeasure (μ i)] {i : ι}
  证明: integrable_comp_eval h

Depends on / 依赖: integrable_comp_eval
-/
lemma integrable_eval [forall i, NormedAddCommGroup (X i)] [forall i, IsFiniteMeasure (μ i)] {i : ι}
    (h : Integrable id (μ i)) :
    Integrable (fun x => x i) (Measure.pi μ) :=
  integrable_comp_eval h

/--
lemma `integral_comp_eval` / 引理 `integral_comp_eval`

English:
lemma integral_comp_eval
  statement: [NormedSpace Real E] [forall i, IsProbabilityMeasure (μ i)] {i : ι} {f : X i -> E}
  proof: by
  rw [← (measurePreserving_eval μ i).map_eq]; rw [integral_map]
  · exact Measurable.aemeasurable (by fun_prop)
  · rwa [(measurePreserving_eval μ i).map_eq]

中文:
引理 integral_comp_eval
  结论: [NormedSpace 实数 E] [对任意 i, IsProbabilityMeasure (μ i)] {i : ι} {f : X i -> E}
  证明: by
  rw [← (measurePreserving_eval μ i).map_eq]; rw [integral_map]
  · exact Measurable.aemeasurable (by fun_prop)
  · rwa [(measurePreserving_eval μ i).map_eq]

Depends on / 依赖: Measurable, Measurable.aemeasurable, aemeasurable, fun_prop, integral_map, map_eq, measurePreserving_eval
-/
lemma integral_comp_eval [NormedSpace Real E] [forall i, IsProbabilityMeasure (μ i)] {i : ι} {f : X i -> E}
    (hf : AEStronglyMeasurable f (μ i)) :
    ∫ x : Π i, X i, f (x i) ∂Measure.pi μ = ∫ x, f x ∂μ i := by
  rw [← (measurePreserving_eval μ i).map_eq]; rw [integral_map]
  · exact Measurable.aemeasurable (by fun_prop)
  · rwa [(measurePreserving_eval μ i).map_eq]

/--
lemma `integral_eval` / 引理 `integral_eval`

English:
lemma integral_eval
  statement: [forall i, NormedAddCommGroup (X i)] [forall i, NormedSpace Real (X i)]
  proof: integral_comp_eval aestronglyMeasurable_id

中文:
引理 integral_eval
  结论: [对任意 i, NormedAddCommGroup (X i)] [对任意 i, NormedSpace 实数 (X i)]
  证明: integral_comp_eval aestronglyMeasurable_id

Depends on / 依赖: aestronglyMeasurable_id, integral_comp_eval
-/
lemma integral_eval [forall i, NormedAddCommGroup (X i)] [forall i, NormedSpace Real (X i)]
    [forall i, IsProbabilityMeasure (μ i)] {i : ι} [OpensMeasurableSpace (X i)]
    [SecondCountableTopology (X i)] :
    ∫ x, x i ∂Measure.pi μ = ∫ x, x ∂μ i :=
  integral_comp_eval aestronglyMeasurable_id

end MeasureTheory
