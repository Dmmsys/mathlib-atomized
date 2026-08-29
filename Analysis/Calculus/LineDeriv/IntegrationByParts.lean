/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration by parts for line derivatives

Let `f, g : E → ℝ` be two differentiable functions on a real vector space endowed with a Haar
measure. Then `∫ f * g' = - ∫ f' * g`, where `f'` and `g'` denote the derivatives of `f` and `g`
in a given direction `v`, provided that `f * g`, `f' * g` and `f * g'` are all integrable.

In this file, we prove this theorem as well as more general versions where the multiplication is
replaced by a general continuous bilinear form, giving versions both for the line derivative and
the Fréchet derivative. These results are derived from the one-dimensional version and a Fubini
argument.

## Main statements

* `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`: integration by parts
  in terms of line derivatives, with `HasLineDerivAt` assumptions and general bilinear form.
* `integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable`: integration by parts
  in terms of Fréchet derivatives, with `HasFDerivAt` assumptions and general bilinear form.
* `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`: integration by parts
  in terms of Fréchet derivatives, written with `fderiv` assumptions and general bilinear form.
* `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`: integration by parts for scalar
  action, in terms of Fréchet derivatives, written with `fderiv` assumptions.
* `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`: integration by parts for scalar
  multiplication, in terms of Fréchet derivatives, written with `fderiv` assumptions.

## Implementation notes

A standard set of assumptions for integration by parts in a finite-dimensional real vector
space (without boundary term) is that the functions tend to zero at infinity and have integrable
derivatives. In this file, we instead assume that the functions are integrable and have integrable
derivatives. These sets of assumptions are not directly comparable (an integrable function with
integrable derivative does *not* have to tend to zero at infinity). The one we use is geared
towards applications to Fourier transforms.

TODO: prove similar theorems assuming that the functions tend to zero at infinity and have
integrable derivatives.
-/

public section

open MeasureTheory Measure Module Topology

variable {E F G W : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup F]
  [NormedSpace Real F] [NormedAddCommGroup G] [NormedSpace Real G] [NormedAddCommGroup W]
  [NormedSpace Real W] [MeasurableSpace E] {μ : Measure E}

/--
lemma `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1` / 引理 `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1`

English:
lemma integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1
  statement: [SigmaFinite μ]
  proof: calc
  ∫ x, B (f x) (g' x) ∂(μ.prod volume)
    = ∫ x, (∫ t, B (f (x, t)) (g' (x, t))) ∂μ := integral_prod _ hfg'
  _ = ∫ x, (- ∫ t, B (f' (x, t)) (g (x, t))) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf'g.prod_right_ae, hfg'.prod_right_ae, hfg.prod_right_ae]
      with x hf'gx hfg'x hfgx
    apply integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable ?_ ?_ hfg'x hf'gx hfgx
    · intro t ht
      have : (x, t) in tsupport g :=
        tsupport_comp_subset_preimage (f := fun y => (x, y)) g (by fun_prop) ht
      convert! (hf (x, t) this).scomp_of_eq t ((hasDerivAt_id t).add (hasDerivAt_const t (-t)))
        (by simp) <;> simp
    · intro t ht
      have : (x, t) in tsupport f :=
        tsupport_comp_subset_preimage (f := fun y => (x, y)) f (by fun_prop) ht
      convert!
        (hg (x, t) this).scomp_of_eq t ((hasDerivAt_id t).add (hasDerivAt_const t (-t)))
          (by simp) <;> simp
  _ = - ∫ x, B (f' x) (g x) ∂(μ.prod volume) := by rw [integral_neg, integral_prod _ hf'g]

中文:
引理 integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1
  结论: [σ有限 μ]
  证明: calc
  ∫ x, B (f x) (g' x) ∂(μ.prod volume)
    = ∫ x, (∫ t, B (f (x, t)) (g' (x, t))) ∂μ := integral_prod _ hfg'
  _ = ∫ x, (- ∫ t, B (f' (x, t)) (g (x, t))) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf'g.prod_right_ae, hfg'.prod_right_ae, hfg.prod_right_ae]
      with x hf'gx hfg'x hfgx
    apply integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable ?_ ?_ hfg'x hf'gx hfgx
    · intro t ht
      have : (x, t) in tsupport g :=
        tsupport_comp_subset_preimage (f := fun y => (x, y)) g (by fun_prop) ht
      convert! (hf (x, t) this).scomp_of_eq t ((hasDerivAt_id t).add (hasDerivAt_const t (-t)))
        (by simp) <;> simp
    · intro t ht
      have : (x, t) in tsupport f :=
        tsupport_comp_subset_preimage (f := fun y => (x, y)) f (by fun_prop) ht
      convert!
        (hg (x, t) this).scomp_of_eq t ((hasDerivAt_id t).add (hasDerivAt_const t (-t)))
          (by simp) <;> simp
  _ = - ∫ x, B (f' x) (g x) ∂(μ.prod volume) := by rw [integral_neg, integral_prod _ hf'g]
-/
lemma integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1 [SigmaFinite μ]
    {f f' : E × Real -> F} {g g' : E × Real -> G} {B : F ->L[Real] G ->L[Real] W}
    (hf'g : Integrable (fun x => B (f' x) (g x)) (μ.prod volume))
    (hfg' : Integrable (fun x => B (f x) (g' x)) (μ.prod volume))
    (hfg : Integrable (fun x => B (f x) (g x)) (μ.prod volume))
    (hf : forall x in tsupport g, HasLineDerivAt Real f (f' x) x (0, 1))
    (hg : forall x in tsupport f, HasLineDerivAt Real g (g' x) x (0, 1)) :
    ∫ x, B (f x) (g' x) ∂(μ.prod volume) = - ∫ x, B (f' x) (g x) ∂(μ.prod volume) := calc
  ∫ x, B (f x) (g' x) ∂(μ.prod volume)
    = ∫ x, (∫ t, B (f (x, t)) (g' (x, t))) ∂μ := integral_prod _ hfg'
  _ = ∫ x, (- ∫ t, B (f' (x, t)) (g (x, t))) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf'g.prod_right_ae, hfg'.prod_right_ae, hfg.prod_right_ae]
      with x hf'gx hfg'x hfgx
    apply integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable ?_ ?_ hfg'x hf'gx hfgx
    · intro t ht
      have : (x, t) in tsupport g :=
        tsupport_comp_subset_preimage (f := fun y => (x, y)) g (by fun_prop) ht
      convert! (hf (x, t) this).scomp_of_eq t ((hasDerivAt_id t).add (hasDerivAt_const t (-t)))
        (by simp) <;> simp
    · intro t ht
      have : (x, t) in tsupport f :=
        tsupport_comp_subset_preimage (f := fun y => (x, y)) f (by fun_prop) ht
      convert!
        (hg (x, t) this).scomp_of_eq t ((hasDerivAt_id t).add (hasDerivAt_const t (-t)))
          (by simp) <;> simp
  _ = - ∫ x, B (f' x) (g x) ∂(μ.prod volume) := by rw [integral_neg, integral_prod _ hf'g]

variable [BorelSpace E]

/--
lemma `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2` / 引理 `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2`

English:
lemma integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2
  proof: by
  let ν : Measure E := addHaar
  have A : ν.prod volume = (addHaarScalarFactor (ν.prod volume) μ) • μ :=
    isAddLeftInvariant_eq_smul _ _
  have Hf'g : Integrable (fun x => B (f' x) (g x)) (ν.prod volume) := by
    rw [A]; exact hf'g.smul_measure_nnreal
  have Hfg' : Integrable (fun x => B (f x) (g' x)) (ν.prod volume) := by
    rw [A]; exact hfg'.smul_measure_nnreal
  have Hfg : Integrable (fun x => B (f x) (g x)) (ν.prod volume) := by
    rw [A]; exact hfg.smul_measure_nnreal
  rw [isAddLeftInvariant_eq_smul μ (ν.prod volume)]
  simp [integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1 Hf'g Hfg' Hfg hf hg]

中文:
引理 integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2
  证明: by
  let ν : Measure E := addHaar
  have A : ν.prod volume = (addHaarScalarFactor (ν.prod volume) μ) • μ :=
    isAddLeftInvariant_eq_smul _ _
  have Hf'g : Integrable (fun x => B (f' x) (g x)) (ν.prod volume) := by
    rw [A]; exact hf'g.smul_measure_nnreal
  have Hfg' : Integrable (fun x => B (f x) (g' x)) (ν.prod volume) := by
    rw [A]; exact hfg'.smul_measure_nnreal
  have Hfg : Integrable (fun x => B (f x) (g x)) (ν.prod volume) := by
    rw [A]; exact hfg.smul_measure_nnreal
  rw [isAddLeftInvariant_eq_smul μ (ν.prod volume)]
  simp [integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1 Hf'g Hfg' Hfg hf hg]

Depends on / 依赖: Integrable, Measure, addHaar, addHaarScalarFactor, g.smul_measure_nnreal, hfg.smul_measure_nnreal, isAddLeftInvariant_eq_smul, smul_measure_nnreal, volume
-/
lemma integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2
    [FiniteDimensional Real E] {μ : Measure (E × Real)} [IsAddHaarMeasure μ]
    {f f' : E × Real -> F} {g g' : E × Real -> G} {B : F ->L[Real] G ->L[Real] W}
    (hf'g : Integrable (fun x => B (f' x) (g x)) μ)
    (hfg' : Integrable (fun x => B (f x) (g' x)) μ)
    (hfg : Integrable (fun x => B (f x) (g x)) μ)
    (hf : forall x in tsupport g, HasLineDerivAt Real f (f' x) x (0, 1))
    (hg : forall x in tsupport f, HasLineDerivAt Real g (g' x) x (0, 1)) :
    ∫ x, B (f x) (g' x) ∂μ = - ∫ x, B (f' x) (g x) ∂μ := by
  let ν : Measure E := addHaar
  have A : ν.prod volume = (addHaarScalarFactor (ν.prod volume) μ) • μ :=
    isAddLeftInvariant_eq_smul _ _
  have Hf'g : Integrable (fun x => B (f' x) (g x)) (ν.prod volume) := by
    rw [A]; exact hf'g.smul_measure_nnreal
  have Hfg' : Integrable (fun x => B (f x) (g' x)) (ν.prod volume) := by
    rw [A]; exact hfg'.smul_measure_nnreal
  have Hfg : Integrable (fun x => B (f x) (g x)) (ν.prod volume) := by
    rw [A]; exact hfg.smul_measure_nnreal
  rw [isAddLeftInvariant_eq_smul μ (ν.prod volume)]
  simp [integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1 Hf'g Hfg' Hfg hf hg]

variable [FiniteDimensional Real E] [IsAddHaarMeasure μ]

/--
theorem `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable` / 定理 `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`

English:
theorem integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
  proof: by
  by_cases hW : CompleteSpace W; swap
  · simp [integral, hW]
  rcases eq_or_ne v 0 with rfl | hv
  · have Hf' x : B (f' x) (g x) = 0 := by
      by_cases hx : x in tsupport g
      · simp [(hasLineDerivAt_zero (f := f) (x := x)).lineDeriv, (hf x hx).lineDeriv.symm]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have Hg' x : B (f x) (g' x) = 0 := by
      by_cases hx : x in tsupport f
      · simp [(hasLineDerivAt_zero (f := g) (x := x)).lineDeriv, (hg x hx).lineDeriv.symm]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    simp [Hf', Hg']
  have : Nontrivial E := nontrivial_iff.2 ⟨v, 0, hv⟩
  let n := finrank Real E
  let E' := Fin (n - 1) -> Real
  obtain ⟨L, hL⟩ : exists L : E ≃L[Real] (E' × Real), L v = (0, 1) := by
    have : finrank Real (E' × Real) = n := by simpa [this, E'] using Nat.sub_add_cancel finrank_pos
    have L₀ : E ≃L[Real] (E' × Real) := (ContinuousLinearEquiv.ofFinrankEq this).symm
    obtain ⟨M, hM⟩ : exists M : (E' × Real) ≃L[Real] (E' × Real), M (L₀ v) = (0, 1) := by
      apply SeparatingDual.exists_continuousLinearEquiv_apply_eq
      · simpa using hv
      · simp
    exact ⟨L₀.trans M, by simp [hM]⟩
  let ν := Measure.map L μ
  suffices H : ∫ (x : E' × Real), (B (f (L.symm x))) (g' (L.symm x)) ∂ν =
      -∫ (x : E' × Real), (B (f' (L.symm x))) (g (L.symm x)) ∂ν by
    have : μ = Measure.map L.symm ν := by
      simp [ν, Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
    have hL : IsClosedEmbedding L.symm := L.symm.toHomeomorph.isClosedEmbedding
    simpa [this, hL.integral_map] using H
  have L_emb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hf'g
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hfg'
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hfg
  · intro x hx
    have : f = (f ∘ L.symm) ∘ (L : E ->ₗ[Real] (E' × Real)) := by ext y; simp
    have h2x : L.symm x in tsupport g :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage g L.symm.toHomeomorph) x).mp hx
    specialize hf (L.symm x) h2x
    rw [this] at hf
    convert! hf.of_comp using 1
    · simp
    · simp [← hL]
  · intro x hx
    have : g = (g ∘ L.symm) ∘ (L : E ->ₗ[Real] (E' × Real)) := by ext y; simp
    have h2x : L.symm x in tsupport f :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage f L.symm.toHomeomorph) x).mp hx
    specialize hg (L.symm x) h2x
    rw [this] at hg
    convert! hg.of_comp using 1
    · simp
    · simp [← hL]

中文:
定理 integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
  证明: by
  by_cases hW : CompleteSpace W; swap
  · simp [integral, hW]
  rcases eq_or_ne v 0 with rfl | hv
  · have Hf' x : B (f' x) (g x) = 0 := by
      by_cases hx : x in tsupport g
      · simp [(hasLineDerivAt_zero (f := f) (x := x)).lineDeriv, (hf x hx).lineDeriv.symm]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have Hg' x : B (f x) (g' x) = 0 := by
      by_cases hx : x in tsupport f
      · simp [(hasLineDerivAt_zero (f := g) (x := x)).lineDeriv, (hg x hx).lineDeriv.symm]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    simp [Hf', Hg']
  have : Nontrivial E := nontrivial_iff.2 ⟨v, 0, hv⟩
  let n := finrank Real E
  let E' := Fin (n - 1) -> Real
  obtain ⟨L, hL⟩ : exists L : E ≃L[Real] (E' × Real), L v = (0, 1) := by
    have : finrank Real (E' × Real) = n := by simpa [this, E'] using Nat.sub_add_cancel finrank_pos
    have L₀ : E ≃L[Real] (E' × Real) := (ContinuousLinearEquiv.ofFinrankEq this).symm
    obtain ⟨M, hM⟩ : exists M : (E' × Real) ≃L[Real] (E' × Real), M (L₀ v) = (0, 1) := by
      apply SeparatingDual.exists_continuousLinearEquiv_apply_eq
      · simpa using hv
      · simp
    exact ⟨L₀.trans M, by simp [hM]⟩
  let ν := Measure.map L μ
  suffices H : ∫ (x : E' × Real), (B (f (L.symm x))) (g' (L.symm x)) ∂ν =
      -∫ (x : E' × Real), (B (f' (L.symm x))) (g (L.symm x)) ∂ν by
    have : μ = Measure.map L.symm ν := by
      simp [ν, Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
    have hL : IsClosedEmbedding L.symm := L.symm.toHomeomorph.isClosedEmbedding
    simpa [this, hL.integral_map] using H
  have L_emb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hf'g
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hfg'
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hfg
  · intro x hx
    have : f = (f ∘ L.symm) ∘ (L : E ->ₗ[Real] (E' × Real)) := by ext y; simp
    have h2x : L.symm x in tsupport g :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage g L.symm.toHomeomorph) x).mp hx
    specialize hf (L.symm x) h2x
    rw [this] at hf
    convert! hf.of_comp using 1
    · simp
    · simp [← hL]
  · intro x hx
    have : g = (g ∘ L.symm) ∘ (L : E ->ₗ[Real] (E' × Real)) := by ext y; simp
    have h2x : L.symm x in tsupport f :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage f L.symm.toHomeomorph) x).mp hx
    specialize hg (L.symm x) h2x
    rw [this] at hg
    convert! hg.of_comp using 1
    · simp
    · simp [← hL]

Depends on / 依赖: CompleteSpace, eq_or_ne, hasLineDerivAt_zero, image_eq_zero_of_notMem_tsupport, integral, lineDeriv, lineDeriv.symm, tsupport
-/
theorem integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    {f f' : E -> F} {g g' : E -> G} {v : E} {B : F ->L[Real] G ->L[Real] W}
    (hf'g : Integrable (fun x => B (f' x) (g x)) μ) (hfg' : Integrable (fun x => B (f x) (g' x)) μ)
    (hfg : Integrable (fun x => B (f x) (g x)) μ)
    (hf : forall x in tsupport g, HasLineDerivAt Real f (f' x) x v)
    (hg : forall x in tsupport f, HasLineDerivAt Real g (g' x) x v) :
    ∫ x, B (f x) (g' x) ∂μ = - ∫ x, B (f' x) (g x) ∂μ := by
  by_cases hW : CompleteSpace W; swap
  · simp [integral, hW]
  rcases eq_or_ne v 0 with rfl | hv
  · have Hf' x : B (f' x) (g x) = 0 := by
      by_cases hx : x in tsupport g
      · simp [(hasLineDerivAt_zero (f := f) (x := x)).lineDeriv, (hf x hx).lineDeriv.symm]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have Hg' x : B (f x) (g' x) = 0 := by
      by_cases hx : x in tsupport f
      · simp [(hasLineDerivAt_zero (f := g) (x := x)).lineDeriv, (hg x hx).lineDeriv.symm]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    simp [Hf', Hg']
  have : Nontrivial E := nontrivial_iff.2 ⟨v, 0, hv⟩
  let n := finrank Real E
  let E' := Fin (n - 1) -> Real
  obtain ⟨L, hL⟩ : exists L : E ≃L[Real] (E' × Real), L v = (0, 1) := by
    have : finrank Real (E' × Real) = n := by simpa [this, E'] using Nat.sub_add_cancel finrank_pos
    have L₀ : E ≃L[Real] (E' × Real) := (ContinuousLinearEquiv.ofFinrankEq this).symm
    obtain ⟨M, hM⟩ : exists M : (E' × Real) ≃L[Real] (E' × Real), M (L₀ v) = (0, 1) := by
      apply SeparatingDual.exists_continuousLinearEquiv_apply_eq
      · simpa using hv
      · simp
    exact ⟨L₀.trans M, by simp [hM]⟩
  let ν := Measure.map L μ
  suffices H : ∫ (x : E' × Real), (B (f (L.symm x))) (g' (L.symm x)) ∂ν =
      -∫ (x : E' × Real), (B (f' (L.symm x))) (g (L.symm x)) ∂ν by
    have : μ = Measure.map L.symm ν := by
      simp [ν, Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
    have hL : IsClosedEmbedding L.symm := L.symm.toHomeomorph.isClosedEmbedding
    simpa [this, hL.integral_map] using H
  have L_emb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hf'g
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hfg'
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hfg
  · intro x hx
    have : f = (f ∘ L.symm) ∘ (L : E ->ₗ[Real] (E' × Real)) := by ext y; simp
    have h2x : L.symm x in tsupport g :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage g L.symm.toHomeomorph) x).mp hx
    specialize hf (L.symm x) h2x
    rw [this] at hf
    convert! hf.of_comp using 1
    · simp
    · simp [← hL]
  · intro x hx
    have : g = (g ∘ L.symm) ∘ (L : E ->ₗ[Real] (E' × Real)) := by ext y; simp
    have h2x : L.symm x in tsupport f :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage f L.symm.toHomeomorph) x).mp hx
    specialize hg (L.symm x) h2x
    rw [this] at hg
    convert! hg.of_comp using 1
    · simp
    · simp [← hL]

/--
theorem `integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable` / 定理 `integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable`

English:
theorem integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
  proof: integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable hf'g hfg' hfg
    (hf · · |>.hasLineDerivAt v) (hg · · |>.hasLineDerivAt v)

中文:
定理 integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
  证明: integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable hf'g hfg' hfg
    (hf · · |>.hasLineDerivAt v) (hg · · |>.hasLineDerivAt v)

Depends on / 依赖: hasLineDerivAt, integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
-/
theorem integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    {f : E -> F} {f' : E -> (E ->L[Real] F)}
    {g : E -> G} {g' : E -> (E ->L[Real] G)} {v : E} {B : F ->L[Real] G ->L[Real] W}
    (hf'g : Integrable (fun x => B (f' x v) (g x)) μ)
    (hfg' : Integrable (fun x => B (f x) (g' x v)) μ)
    (hfg : Integrable (fun x => B (f x) (g x)) μ)
    (hf : forall x in tsupport g, HasFDerivAt f (f' x) x)
    (hg : forall x in tsupport f, HasFDerivAt g (g' x) x) :
    ∫ x, B (f x) (g' x v) ∂μ = - ∫ x, B (f' x v) (g x) ∂μ :=
  integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable hf'g hfg' hfg
    (hf · · |>.hasLineDerivAt v) (hg · · |>.hasLineDerivAt v)

/--
theorem `integral_bilinear_fderiv_right_eq_neg_left_of_integrable` / 定理 `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`

English:
theorem integral_bilinear_fderiv_right_eq_neg_left_of_integrable
  proof: integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable hf'g hfg' hfg
    (hf · · |>.hasFDerivAt) (hg · · |>.hasFDerivAt)

中文:
定理 integral_bilinear_fderiv_right_eq_neg_left_of_integrable
  证明: integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable hf'g hfg' hfg
    (hf · · |>.hasFDerivAt) (hg · · |>.hasFDerivAt)

Depends on / 依赖: hasFDerivAt, integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
-/
theorem integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    {f : E -> F} {g : E -> G} {v : E} {B : F ->L[Real] G ->L[Real] W}
    (hf'g : Integrable (fun x => B (fderiv Real f x v) (g x)) μ)
    (hfg' : Integrable (fun x => B (f x) (fderiv Real g x v)) μ)
    (hfg : Integrable (fun x => B (f x) (g x)) μ)
    (hf : forall x in tsupport g, DifferentiableAt Real f x)
    (hg : forall x in tsupport f, DifferentiableAt Real g x) :
    ∫ x, B (f x) (fderiv Real g x v) ∂μ = - ∫ x, B (fderiv Real f x v) (g x) ∂μ :=
  integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable hf'g hfg' hfg
    (hf · · |>.hasFDerivAt) (hg · · |>.hasFDerivAt)

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra Real 𝕜]
    [NormedSpace 𝕜 G] [IsScalarTower Real 𝕜 G]

/--
theorem `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable` / 定理 `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`

English:
theorem integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
  proof: integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.lsmul Real 𝕜) hf'g hfg' hfg hf hg

中文:
定理 integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
  证明: integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.lsmul Real 𝕜) hf'g hfg' hfg hf hg

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, integral_bilinear_fderiv_right_eq_neg_left_of_integrable
-/
theorem integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    {f : E -> 𝕜} {g : E -> G} {v : E}
    (hf'g : Integrable (fun x => fderiv Real f x v • g x) μ)
    (hfg' : Integrable (fun x => f x • fderiv Real g x v) μ)
    (hfg : Integrable (fun x => f x • g x) μ)
    (hf : forall x in tsupport g, DifferentiableAt Real f x)
    (hg : forall x in tsupport f, DifferentiableAt Real g x) :
    ∫ x, f x • fderiv Real g x v ∂μ = - ∫ x, fderiv Real f x v • g x ∂μ :=
  integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.lsmul Real 𝕜) hf'g hfg' hfg hf hg

/--
theorem `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` / 定理 `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`

English:
theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  proof: integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul Real 𝕜) hf'g hfg' hfg hf hg

中文:
定理 integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  证明: integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul Real 𝕜) hf'g hfg' hfg hf hg

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, integral_bilinear_fderiv_right_eq_neg_left_of_integrable
-/
theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    {f : E -> 𝕜} {g : E -> 𝕜} {v : E}
    (hf'g : Integrable (fun x => fderiv Real f x v * g x) μ)
    (hfg' : Integrable (fun x => f x * fderiv Real g x v) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hf : forall x in tsupport g, DifferentiableAt Real f x)
    (hg : forall x in tsupport f, DifferentiableAt Real g x) :
    ∫ x, f x * fderiv Real g x v ∂μ = - ∫ x, fderiv Real f x v * g x ∂μ :=
  integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul Real 𝕜) hf'g hfg' hfg hf hg
