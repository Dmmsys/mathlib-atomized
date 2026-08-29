/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
public import Mathlib.Probability.Independence.Process.Basic
public import Mathlib.Probability.Notation

/-!
# Characterizing independence via bounded continuous functions

Given two random variables `X : Ω → E` and `Y : Ω → F` such that `E` and `F` are Borel spaces
satisfying `HasOuterApproxClosed`, `X` and `Y` are independent if for any real bounded continuous
functions `f` and `g`, `∫ ω, f (X ω) * g (Y ω) ∂P = (∫ ω, f (X ω) ∂P) * (∫ ω, g (Y ω) ∂P)`.

Consider now `X : (s : S) → Ω → E s`, with `Fintype S` and each `E s` being a Borel space satisfying
`HasOuterApproxClosed`. Then to apply the above result we need that `Π s, E s` is a Borel space,
and therefore that each `E s` is second countable. We can circumvent this restriction by proving
that `fun ω s ↦ X s ω` and `Y` are independent if for any family of bounded continuous functions
`f : (s : S) → E s → ℝ` and any bounded continuous function `g : F → ℝ` we have
`∫ ω, ∏ s, f s (X s ω) * g (Y ω) ∂P = ∫ ω, ∏ s, f s (X s ω) ∂P * ∫ ω, g (Y ω) ∂P`.
We can use this result in the case where `S := Unit` to deduce the first statement we mentioned.

We take this approach in this file. We first prove `pi_indepFun_pi_of_prod_bcf`, which allows to
prove the result when `E` and `F` are product spaces without assuming second countability, and
then we deduce the other cases from there.

Building on this, we also prove `process_indepFun_process_of_prod_bcf`. This time we do not require
`Fintype S` and require the hypothesis to be satisfied for each `I : Finset S`. Then we similarly
deduce other versions where one of the variables is not necessarily a process.

We then turn to independence between an event and a random variable. We prove
`indicator_indepFun_pi_of_prod_bcf`: the indicator of an event `A` is independent
of a finite family of random variables `X : (s : S) → Ω → E s` if for any family of bounded
continuous functions `f : (s : S) → E s → ℝ` we have
`∫ ω in A, ∏ s, f s (X s ω) ∂P = P.real A * ∫ ω, ∏ s, f s (X s ω) ∂P`. Once again we deduce
other versions from this, and also write versions where `X` is a stochastic process.

Then we build on that to show that a `σ`-algebra `m` is independent from a stochastic process `X`
if for any `A` such that `MeasurableSet[m] A`, any `I : Finset S` and any bounded continuous
function `f : (Π s : I, E s) → ℝ`, we have `∫ ω in A, f (X · ω) ∂P = P.real A * ∫ ω, f (X · ω) ∂P`.
This again is formulated with different versions. We also provide versions in terms of
`IndepSets` instead of `Indep`.

## Main statement

* `indep_comap_process_of_bcf`: A `σ`-algebra `m` is independent from a stochastic process `X`
  if for any `A` such that `MeasurableSet[m] A`, any `I : Finset S`, and any bounded continuous
  function `f : (Π s : I, E s) → ℝ`, we have
  `∫ ω in A, f (X · ω) ∂P = P.real A * ∫ ω, f (X · ω) ∂P`.

## Notations

to avoid writing `boundedContinuousFunction` in the names, which is quite lengthy, we abbreviate it
to `bcf`.

## Tags

independence, bounded continuous functions
-/

public section

open MeasureTheory Measure ProbabilityTheory ENNReal
open scoped BoundedContinuousFunction

variable {Ω S T : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

/--
lemma `IndepFun.singleton_indepSets_of_indicator` / 引理 `IndepFun.singleton_indepSets_of_indicator`

English:
lemma IndepFun.singleton_indepSets_of_indicator
  statement: {𝓧 : Type*} [mX : MeasurableSpace 𝓧] {A : Set Ω}
  proof: by
  rw [IndepSets_iff]
  rintro s - hs ⟨t, ht, rfl⟩
  rw [Set.mem_singleton_iff.1 hs]
  have hA' : A = A.indicator (1 : Ω -> Real) ⁻¹' {1} := by ext; simp [Set.indicator]
  rw [hA']
  exact h.measure_inter_preimage_eq_mul _ _ (by simp) ht

中文:
引理 IndepFun.singleton_indepSets_of_indicator
  结论: {𝓧 : 类型} [mX : 可测空间 𝓧] {A : 集合 Ω}
  证明: by
  rw [IndepSets_iff]
  rintro s - hs ⟨t, ht, rfl⟩
  rw [Set.mem_singleton_iff.1 hs]
  have hA' : A = A.indicator (1 : Ω -> Real) ⁻¹' {1} := by ext; simp [Set.indicator]
  rw [hA']
  exact h.measure_inter_preimage_eq_mul _ _ (by simp) ht

Depends on / 依赖: A.indicator, IndepSets_iff, Set.indicator, Set.mem_singleton_iff, h.measure_inter_preimage_eq_mul, indicator, measure_inter_preimage_eq_mul, mem_singleton_iff
-/
lemma IndepFun.singleton_indepSets_of_indicator {𝓧 : Type*} [mX : MeasurableSpace 𝓧] {A : Set Ω}
    {X : Ω -> 𝓧} (h : (A.indicator (1 : Ω -> Real)) ⟂ᵢ[P] X) :
    IndepSets {A} {s | MeasurableSet[mX.comap X] s} P := by
  rw [IndepSets_iff]
  rintro s - hs ⟨t, ht, rfl⟩
  rw [Set.mem_singleton_iff.1 hs]
  have hA' : A = A.indicator (1 : Ω -> Real) ⁻¹' {1} := by ext; simp [Set.indicator]
  rw [hA']
  exact h.measure_inter_preimage_eq_mul _ _ (by simp) ht

variable {E : S -> Type*} {F : T -> Type*} {G H : Type*}
  [forall s, TopologicalSpace (E s)] [forall s, MeasurableSpace (E s)] [forall s, BorelSpace (E s)]
  [forall s, HasOuterApproxClosed (E s)]
  [forall t, TopologicalSpace (F t)] [forall t, MeasurableSpace (F t)] [forall t, BorelSpace (F t)]
  [forall t, HasOuterApproxClosed (F t)]
  [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [HasOuterApproxClosed G]
  [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [HasOuterApproxClosed H]
  {X : (s : S) -> Ω -> E s} {Y : (t : T) -> Ω -> F t} {Z : Ω -> G} {U : Ω -> H}

section Fintype

variable [Fintype S] [Fintype T]

section IndepFun

variable [IsFiniteMeasure P]

/--
lemma `pi_indepFun_pi_of_prod_bcf` / 引理 `pi_indepFun_pi_of_prod_bcf`

English:
lemma pi_indepFun_pi_of_prod_bcf
  statement: (mX : forall s, AEMeasurable (X s) P)
  proof: by
  rw [indepFun_iff_map_prod_eq_prod_map_map (aemeasurable_pi_lambda _ mX)
    (aemeasurable_pi_lambda _ mY)]
  refine eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction fun f g => ?_
  rw [integral_map]; rw [integral_map]; rw [integral_map]
  · convert! h f g <;> simp
  any_goals fun_pro

中文:
引理 pi_indepFun_pi_of_prod_bcf
  结论: (mX : 对任意 s, 几乎处处可测 (X s) P)
  证明: by
  rw [indepFun_iff_map_prod_eq_prod_map_map (aemeasurable_pi_lambda _ mX)
    (aemeasurable_pi_lambda _ mY)]
  refine eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction fun f g => ?_
  rw [integral_map]; rw [integral_map]; rw [integral_map]
  · convert! h f g <;> simp
  any_goals fun_pro

Depends on / 依赖: Measurable, Measurable.aestronglyMeasurable, aemeasurable_pi_lambda, aestronglyMeasurable, all_goals, any_goals, convert, eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction, fun_prop, indepFun_iff_map_prod_eq_prod_map_map, integral_map
-/
lemma pi_indepFun_pi_of_prod_bcf (mX : forall s, AEMeasurable (X s) P)
    (mY : forall t, AEMeasurable (Y t) P)
    (h : forall (f : (s : S) -> E s ->ᵇ Real) (g : (t : T) -> F t ->ᵇ Real),
      P[(∏ s, f s ∘ (X s)) * (∏ t, g t ∘ (Y t))] = P[∏ s, f s ∘ (X s)] * P[∏ t, g t ∘ (Y t)]) :
    IndepFun (fun ω s => X s ω) (fun ω t => Y t ω) P := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (aemeasurable_pi_lambda _ mX)
    (aemeasurable_pi_lambda _ mY)]
  refine eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction fun f g => ?_
  rw [integral_map]; rw [integral_map]; rw [integral_map]
  · convert! h f g <;> simp
  any_goals fun_prop
  all_goals exact Measurable.aestronglyMeasurable (by fun_prop)

omit [Fintype S] [Fintype T] in variable [Finite S] [Finite T] in
/--
lemma `pi_indepFun_pi_of_bcf` / 引理 `pi_indepFun_pi_of_bcf`

English:
lemma pi_indepFun_pi_of_bcf
  statement: (mX : forall s, AEMeasurable (X s) P)
  proof: by
  have := Fintype.ofFinite S; have := Fintype.ofFinite T
  refine pi_indepFun_pi_of_prod_bcf mX mY fun f g => ?_
  convert!
    h (∏ s, (f s).compContinuous ⟨Function.eval s, by fun_prop⟩)
      (∏ t, (g t).compContinuous ⟨Function.eval t, by fun_prop⟩) <;> simp

中文:
引理 pi_indepFun_pi_of_bcf
  结论: (mX : 对任意 s, 几乎处处可测 (X s) P)
  证明: by
  have := Fintype.ofFinite S; have := Fintype.ofFinite T
  refine pi_indepFun_pi_of_prod_bcf mX mY fun f g => ?_
  convert!
    h (∏ s, (f s).compContinuous ⟨Function.eval s, by fun_prop⟩)
      (∏ t, (g t).compContinuous ⟨Function.eval t, by fun_prop⟩) <;> simp

Depends on / 依赖: Fintype, Fintype.ofFinite, Function, Function.eval, compContinuous, convert, fun_prop, ofFinite, pi_indepFun_pi_of_prod_bcf
-/
lemma pi_indepFun_pi_of_bcf (mX : forall s, AEMeasurable (X s) P)
    (mY : forall t, AEMeasurable (Y t) P)
    (h : forall (f : (Π s, E s) ->ᵇ Real) (g : (Π t, F t) ->ᵇ Real),
      P[fun ω => f (X · ω) * g (Y · ω)] = P[fun ω => f (X · ω)] * P[fun ω => g (Y · ω)]) :
    IndepFun (fun ω s => X s ω) (fun ω t => Y t ω) P := by
  have := Fintype.ofFinite S; have := Fintype.ofFinite T
  refine pi_indepFun_pi_of_prod_bcf mX mY fun f g => ?_
  convert!
    h (∏ s, (f s).compContinuous ⟨Function.eval s, by fun_prop⟩)
      (∏ t, (g t).compContinuous ⟨Function.eval t, by fun_prop⟩) <;> simp

/--
lemma `indepFun_pi_of_prod_bcf` / 引理 `indepFun_pi_of_prod_bcf`

English:
lemma indepFun_pi_of_prod_bcf
  statement: (mZ : AEMeasurable Z P)
  proof: by
  rw [indepFun_iff_map_prod_eq_prod_map_map mZ (aemeasurable_pi_lambda _ mY)]
  refine eq_prod_of_integral_mul_prod_boundedContinuousFunction fun f g => ?_
  rw [integral_map]; rw [integral_map]; rw [integral_map]
  · convert! h f g <;> simp
  any_goals fun_prop
  all_goals exact Measurable.aestr

中文:
引理 indepFun_pi_of_prod_bcf
  结论: (mZ : 几乎处处可测 Z P)
  证明: by
  rw [indepFun_iff_map_prod_eq_prod_map_map mZ (aemeasurable_pi_lambda _ mY)]
  refine eq_prod_of_integral_mul_prod_boundedContinuousFunction fun f g => ?_
  rw [integral_map]; rw [integral_map]; rw [integral_map]
  · convert! h f g <;> simp
  any_goals fun_prop
  all_goals exact Measurable.aestr

Depends on / 依赖: Measurable, Measurable.aestronglyMeasurable, aemeasurable_pi_lambda, aestronglyMeasurable, all_goals, any_goals, convert, eq_prod_of_integral_mul_prod_boundedContinuousFunction, fun_prop, indepFun_iff_map_prod_eq_prod_map_map, integral_map
-/
lemma indepFun_pi_of_prod_bcf (mZ : AEMeasurable Z P)
    (mY : forall t, AEMeasurable (Y t) P)
    (h : forall (f : G ->ᵇ Real) (g : (t : T) -> F t ->ᵇ Real),
      P[f ∘ Z * (∏ t, g t ∘ (Y t))] = P[f ∘ Z] * P[∏ t, g t ∘ (Y t)]) :
    IndepFun Z (fun ω t => Y t ω) P := by
  rw [indepFun_iff_map_prod_eq_prod_map_map mZ (aemeasurable_pi_lambda _ mY)]
  refine eq_prod_of_integral_mul_prod_boundedContinuousFunction fun f g => ?_
  rw [integral_map]; rw [integral_map]; rw [integral_map]
  · convert! h f g <;> simp
  any_goals fun_prop
  all_goals exact Measurable.aestronglyMeasurable (by fun_prop)

omit [Fintype T] in variable [Finite T] in
/--
lemma `indepFun_pi_of_bcf` / 引理 `indepFun_pi_of_bcf`

English:
lemma indepFun_pi_of_bcf
  statement: (mZ : AEMeasurable Z P)
  proof: by
  have := Fintype.ofFinite T
  refine indepFun_pi_of_prod_bcf mZ mY fun f g => ?_
  convert! h f (∏ t, (g t).compContinuous ⟨Function.eval t, by fun_prop⟩) <;> simp

中文:
引理 indepFun_pi_of_bcf
  结论: (mZ : 几乎处处可测 Z P)
  证明: by
  have := Fintype.ofFinite T
  refine indepFun_pi_of_prod_bcf mZ mY fun f g => ?_
  convert! h f (∏ t, (g t).compContinuous ⟨Function.eval t, by fun_prop⟩) <;> simp

Depends on / 依赖: Fintype, Fintype.ofFinite, Function, Function.eval, compContinuous, convert, fun_prop, indepFun_pi_of_prod_bcf, ofFinite
-/
lemma indepFun_pi_of_bcf (mZ : AEMeasurable Z P)
    (mY : forall t, AEMeasurable (Y t) P)
    (h : forall (f : G ->ᵇ Real) (g : (Π t, F t) ->ᵇ Real),
      P[fun ω => f (Z ω) * g (Y · ω)] = P[f ∘ Z] * P[fun ω => g (Y · ω)]) :
    IndepFun Z (fun ω t => Y t ω) P := by
  have := Fintype.ofFinite T
  refine indepFun_pi_of_prod_bcf mZ mY fun f g => ?_
  convert! h f (∏ t, (g t).compContinuous ⟨Function.eval t, by fun_prop⟩) <;> simp

/--
lemma `pi_indepFun_of_prod_bcf` / 引理 `pi_indepFun_of_prod_bcf`

English:
lemma pi_indepFun_of_prod_bcf
  statement: (mX : forall s, AEMeasurable (X s) P)
  proof: by
  rw [indepFun_iff_map_prod_eq_prod_map_map (aemeasurable_pi_lambda _ mX) mU]
  refine eq_prod_of_integral_prod_mul_boundedContinuousFunction fun f g => ?_
  rw [integral_map]; rw [integral_map]; rw [integral_map]
  · convert! h f g <;> simp
  any_goals fun_prop
  all_goals exact Measurable.aestr

中文:
引理 pi_indepFun_of_prod_bcf
  结论: (mX : 对任意 s, 几乎处处可测 (X s) P)
  证明: by
  rw [indepFun_iff_map_prod_eq_prod_map_map (aemeasurable_pi_lambda _ mX) mU]
  refine eq_prod_of_integral_prod_mul_boundedContinuousFunction fun f g => ?_
  rw [integral_map]; rw [integral_map]; rw [integral_map]
  · convert! h f g <;> simp
  any_goals fun_prop
  all_goals exact Measurable.aestr

Depends on / 依赖: Measurable, Measurable.aestronglyMeasurable, aemeasurable_pi_lambda, aestronglyMeasurable, all_goals, any_goals, convert, eq_prod_of_integral_prod_mul_boundedContinuousFunction, fun_prop, indepFun_iff_map_prod_eq_prod_map_map, integral_map
-/
lemma pi_indepFun_of_prod_bcf (mX : forall s, AEMeasurable (X s) P)
    (mU : AEMeasurable U P)
    (h : forall (f : (s : S) -> E s ->ᵇ Real) (g : H ->ᵇ Real),
      P[(∏ s, f s ∘ (X s)) * g ∘ U] = P[∏ s, f s ∘ (X s)] * P[g ∘ U]) :
    IndepFun (fun ω s => X s ω) U P := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (aemeasurable_pi_lambda _ mX) mU]
  refine eq_prod_of_integral_prod_mul_boundedContinuousFunction fun f g => ?_
  rw [integral_map]; rw [integral_map]; rw [integral_map]
  · convert! h f g <;> simp
  any_goals fun_prop
  all_goals exact Measurable.aestronglyMeasurable (by fun_prop)

omit [Fintype S] in variable [Finite S] in
/--
lemma `pi_indepFun_of_bcf` / 引理 `pi_indepFun_of_bcf`

English:
lemma pi_indepFun_of_bcf
  statement: (mX : forall s, AEMeasurable (X s) P)
  proof: by
  have := Fintype.ofFinite S
  refine pi_indepFun_of_prod_bcf mX mU fun f g => ?_
  convert! h (∏ s, (f s).compContinuous ⟨Function.eval s, by fun_prop⟩) g <;> simp

中文:
引理 pi_indepFun_of_bcf
  结论: (mX : 对任意 s, 几乎处处可测 (X s) P)
  证明: by
  have := Fintype.ofFinite S
  refine pi_indepFun_of_prod_bcf mX mU fun f g => ?_
  convert! h (∏ s, (f s).compContinuous ⟨Function.eval s, by fun_prop⟩) g <;> simp

Depends on / 依赖: Fintype, Fintype.ofFinite, Function, Function.eval, compContinuous, convert, fun_prop, ofFinite, pi_indepFun_of_prod_bcf
-/
lemma pi_indepFun_of_bcf (mX : forall s, AEMeasurable (X s) P)
    (mU : AEMeasurable U P)
    (h : forall (f : (Π s, E s) ->ᵇ Real) (g : H ->ᵇ Real),
      P[fun ω => f (X · ω) * g (U ω)] = P[fun ω => f (X · ω)] * P[g ∘ U]) :
    IndepFun (fun ω s => X s ω) U P := by
  have := Fintype.ofFinite S
  refine pi_indepFun_of_prod_bcf mX mU fun f g => ?_
  convert! h (∏ s, (f s).compContinuous ⟨Function.eval s, by fun_prop⟩) g <;> simp

/--
lemma `indepFun_of_bcf` / 引理 `indepFun_of_bcf`

English:
lemma indepFun_of_bcf
  statement: (mZ : AEMeasurable Z P) (mU : AEMeasurable U P)
  proof: by
  rw [indepFun_iff_map_prod_eq_prod_map_map mZ mU]
  refine eq_prod_of_integral_mul_boundedContinuousFunction fun f g => ?_
  rw [integral_map]; rw [integral_map]; rw [integral_map]
  · exact h f g
  any_goals fun_prop
  exact Measurable.aestronglyMeasurable (by fun_prop)

中文:
引理 indepFun_of_bcf
  结论: (mZ : 几乎处处可测 Z P) (mU : 几乎处处可测 U P)
  证明: by
  rw [indepFun_iff_map_prod_eq_prod_map_map mZ mU]
  refine eq_prod_of_integral_mul_boundedContinuousFunction fun f g => ?_
  rw [integral_map]; rw [integral_map]; rw [integral_map]
  · exact h f g
  any_goals fun_prop
  exact Measurable.aestronglyMeasurable (by fun_prop)

Depends on / 依赖: Measurable, Measurable.aestronglyMeasurable, aestronglyMeasurable, any_goals, eq_prod_of_integral_mul_boundedContinuousFunction, fun_prop, indepFun_iff_map_prod_eq_prod_map_map, integral_map
-/
lemma indepFun_of_bcf (mZ : AEMeasurable Z P) (mU : AEMeasurable U P)
    (h : forall (f : G ->ᵇ Real) (g : H ->ᵇ Real), P[f ∘ Z * g ∘ U] = P[f ∘ Z] * P[g ∘ U]) :
    IndepFun Z U P := by
  rw [indepFun_iff_map_prod_eq_prod_map_map mZ mU]
  refine eq_prod_of_integral_mul_boundedContinuousFunction fun f g => ?_
  rw [integral_map]; rw [integral_map]; rw [integral_map]
  · exact h f g
  any_goals fun_prop
  exact Measurable.aestronglyMeasurable (by fun_prop)

end IndepFun

variable [IsProbabilityMeasure P]

section Indicator

/--
lemma `indicator_indepFun_pi_of_prod_bcf` / 引理 `indicator_indepFun_pi_of_prod_bcf`

English:
lemma indicator_indepFun_pi_of_prod_bcf
  proof: by
  refine indepFun_pi_of_prod_bcf
    ((aemeasurable_indicator_const_iff 1).2 mA) mX fun f g => ?_
  have h1 ω : f (A.indicator 1 ω) * ∏ s, g s (X s ω) =
      A.indicator (fun ω => f 1 * ∏ s, g s (X s ω)) ω +
      f 0 * ∏ s, g s (X s ω) - A.indicator (fun ω => f 0 * ∏ s, g s (X s ω)) ω := by
   

中文:
引理 indicator_indepFun_pi_of_prod_bcf
  证明: by
  refine indepFun_pi_of_prod_bcf
    ((aemeasurable_indicator_const_iff 1).2 mA) mX fun f g => ?_
  have h1 ω : f (A.indicator 1 ω) * ∏ s, g s (X s ω) =
      A.indicator (fun ω => f 1 * ∏ s, g s (X s ω)) ω +
      f 0 * ∏ s, g s (X s ω) - A.indicator (fun ω => f 0 * ∏ s, g s (X s ω)) ω := by
   

Depends on / 依赖: A.indicator, Set.indicator_apply, aemeasurable_indicator_const_iff, classical, indepFun_pi_of_prod_bcf, indicator, indicator_apply, split_ifs
-/
lemma indicator_indepFun_pi_of_prod_bcf
    {A : Set Ω} (mA : NullMeasurableSet A P) (mX : forall s, AEMeasurable (X s) P)
    (h : forall f : (s : S) -> E s ->ᵇ Real, ∫ ω in A, ∏ s, f s (X s ω) ∂P =
      P.real A * ∫ ω, ∏ s, f s (X s ω) ∂P) :
    (A.indicator (1 : Ω -> Real)) ⟂ᵢ[P] (fun ω s => X s ω) := by
  refine indepFun_pi_of_prod_bcf
    ((aemeasurable_indicator_const_iff 1).2 mA) mX fun f g => ?_
  have h1 ω : f (A.indicator 1 ω) * ∏ s, g s (X s ω) =
      A.indicator (fun ω => f 1 * ∏ s, g s (X s ω)) ω +
      f 0 * ∏ s, g s (X s ω) - A.indicator (fun ω => f 0 * ∏ s, g s (X s ω)) ω := by
    classical
    rw [Set.indicator_apply]
    split_ifs <;> simp_all
  have h2 ω : f (A.indicator 1 ω) =
      A.indicator (fun _ => f 1) ω + Aᶜ.indicator (fun _ => f 0) ω := by
    classical
    rw [Set.indicator_apply]
    split_ifs <;> simp_all
  have hg {c : Real} : Integrable (fun ω => c * ∏ s, g s (X s ω)) P := by
    refine Integrable.of_bound ?_ (‖c‖ * ∏ s, ‖g s‖) (ae_of_all _ fun ω => ?_)
    · exact (Finset.aestronglyMeasurable_fun_prod _ fun s _ =>
        (g s).continuous.aestronglyMeasurable.comp_aemeasurable (mX s)).const_mul _
    · rw [norm_mul, norm_prod]
      gcongr with s
      exact (g s).norm_coe_le_norm _
  simp_rw [Pi.mul_apply, Finset.prod_apply, Function.comp_apply, h1, h2]
  rw [integral_sub]; rw [integral_add]; rw [integral_indicator₀ mA]; rw [integral_indicator₀ mA]; rw [integral_const_mul]; rw [integral_const_mul]; rw [integral_const_mul]; rw [integral_add]; rw [integral_indicator₀ mA]; rw [integral_indicator₀ mA.compl]; rw [integral_const]; rw [integral_const]; rw [h]
  · simp [measureReal_compl₀ mA]
    ring
  · exact (integrable_const _).indicator₀ mA
  · exact (integrable_const _).indicator₀ mA.compl
  · exact hg.indicator₀ mA
  · exact hg
  · exact (hg.indicator₀ mA).add hg
  · exact hg.indicator₀ mA

omit [Fintype S] in variable [Finite S] in
/--
lemma `indicator_indepFun_pi_of_bcf` / 引理 `indicator_indepFun_pi_of_bcf`

English:
lemma indicator_indepFun_pi_of_bcf
  proof: by
  have := Fintype.ofFinite S
  refine indicator_indepFun_pi_of_prod_bcf mA mX fun f => ?_
  convert! h (∏ s, (f s).compContinuous ⟨Function.eval s, by fun_prop⟩) <;> simp

中文:
引理 indicator_indepFun_pi_of_bcf
  证明: by
  have := Fintype.ofFinite S
  refine indicator_indepFun_pi_of_prod_bcf mA mX fun f => ?_
  convert! h (∏ s, (f s).compContinuous ⟨Function.eval s, by fun_prop⟩) <;> simp

Depends on / 依赖: Fintype, Fintype.ofFinite, Function, Function.eval, compContinuous, convert, fun_prop, indicator_indepFun_pi_of_prod_bcf, ofFinite
-/
lemma indicator_indepFun_pi_of_bcf
    {A : Set Ω} (mA : NullMeasurableSet A P) (mX : forall s, AEMeasurable (X s) P)
    (h : forall f : (Π s, E s) ->ᵇ Real, ∫ ω in A, f (X · ω) ∂P = P.real A * ∫ ω, f (X · ω) ∂P) :
    (A.indicator (1 : Ω -> Real)) ⟂ᵢ[P] (fun ω s => X s ω) := by
  have := Fintype.ofFinite S
  refine indicator_indepFun_pi_of_prod_bcf mA mX fun f => ?_
  convert! h (∏ s, (f s).compContinuous ⟨Function.eval s, by fun_prop⟩) <;> simp

/--
lemma `indicator_indepFun_of_bcf` / 引理 `indicator_indepFun_of_bcf`

English:
lemma indicator_indepFun_of_bcf
  proof: by
  suffices (A.indicator (1 : Ω -> Real)) ⟂ᵢ[P] (fun ω (_ : Unit) => Z ω) from
    this.comp (measurable_id) (measurable_pi_apply ())
  refine indicator_indepFun_pi_of_prod_bcf mA (fun _ => mZ) fun f => ?_
  convert! h (f ()) <;> simp

中文:
引理 indicator_indepFun_of_bcf
  证明: by
  suffices (A.indicator (1 : Ω -> Real)) ⟂ᵢ[P] (fun ω (_ : Unit) => Z ω) from
    this.comp (measurable_id) (measurable_pi_apply ())
  refine indicator_indepFun_pi_of_prod_bcf mA (fun _ => mZ) fun f => ?_
  convert! h (f ()) <;> simp

Depends on / 依赖: A.indicator, convert, indicator, indicator_indepFun_pi_of_prod_bcf, measurable_id, measurable_pi_apply, this.comp
-/
lemma indicator_indepFun_of_bcf
    {A : Set Ω} (mA : NullMeasurableSet A P) (mZ : AEMeasurable Z P)
    (h : forall f : G ->ᵇ Real, ∫ ω in A, f (Z ω) ∂P = P.real A * ∫ ω, f (Z ω) ∂P) :
    (A.indicator (1 : Ω -> Real)) ⟂ᵢ[P] Z := by
  suffices (A.indicator (1 : Ω -> Real)) ⟂ᵢ[P] (fun ω (_ : Unit) => Z ω) from
    this.comp (measurable_id) (measurable_pi_apply ())
  refine indicator_indepFun_pi_of_prod_bcf mA (fun _ => mZ) fun f => ?_
  convert! h (f ()) <;> simp

end Indicator

section IndepSets

/--
lemma `indepSets_comap_pi_of_prod_bcf` / 引理 `indepSets_comap_pi_of_prod_bcf`

English:
lemma indepSets_comap_pi_of_prod_bcf
  proof: indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_pi_of_prod_bcf (m𝒜 A hA) mX (h A hA))

omit [Fintype S] in variable [Finite S] in

中文:
引理 indepSets_comap_pi_of_prod_bcf
  证明: indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_pi_of_prod_bcf (m𝒜 A hA) mX (h A hA))

omit [Fintype S] in variable [Finite S] in

Depends on / 依赖: IndepFun, IndepFun.singleton_indepSets_of_indicator, indepSets_iff_singleton_indepSets, indicator_indepFun_pi_of_prod_bcf, singleton_indepSets_of_indicator
-/
lemma indepSets_comap_pi_of_prod_bcf
    {𝒜 : Set (Set Ω)} (m𝒜 : forall A in 𝒜, NullMeasurableSet A P) (mX : forall s, AEMeasurable (X s) P)
    (h : forall A in 𝒜, forall f : (s : S) -> E s ->ᵇ Real, ∫ ω in A, ∏ s, f s (X s ω) ∂P =
      P.real A * ∫ ω, ∏ s, f s (X s ω) ∂P) :
    IndepSets 𝒜 {A | MeasurableSet[MeasurableSpace.pi.comap (fun ω s => X s ω)] A} P :=
  indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_pi_of_prod_bcf (m𝒜 A hA) mX (h A hA))

omit [Fintype S] in variable [Finite S] in
/--
lemma `indepSets_comap_pi_of_bcf` / 引理 `indepSets_comap_pi_of_bcf`

English:
lemma indepSets_comap_pi_of_bcf
  proof: indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_pi_of_bcf (m𝒜 A hA) mX (h A hA))

中文:
引理 indepSets_comap_pi_of_bcf
  证明: indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_pi_of_bcf (m𝒜 A hA) mX (h A hA))

Depends on / 依赖: IndepFun, IndepFun.singleton_indepSets_of_indicator, indepSets_iff_singleton_indepSets, indicator_indepFun_pi_of_bcf, singleton_indepSets_of_indicator
-/
lemma indepSets_comap_pi_of_bcf
    {𝒜 : Set (Set Ω)} (m𝒜 : forall A in 𝒜, NullMeasurableSet A P) (mX : forall s, AEMeasurable (X s) P)
    (h : forall A in 𝒜, forall f : (Π s, E s) ->ᵇ Real, ∫ ω in A, f (X · ω) ∂P = P.real A * ∫ ω, f (X · ω) ∂P) :
    IndepSets 𝒜 {A | MeasurableSet[MeasurableSpace.pi.comap (fun ω s => X s ω)] A} P :=
  indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_pi_of_bcf (m𝒜 A hA) mX (h A hA))

/--
lemma `indepSets_comap_of_bcf` / 引理 `indepSets_comap_of_bcf`

English:
lemma indepSets_comap_of_bcf
  proof: indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_of_bcf (m𝒜 A hA) mZ (h A hA))

中文:
引理 indepSets_comap_of_bcf
  证明: indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_of_bcf (m𝒜 A hA) mZ (h A hA))

Depends on / 依赖: IndepFun, IndepFun.singleton_indepSets_of_indicator, indepSets_iff_singleton_indepSets, indicator_indepFun_of_bcf, singleton_indepSets_of_indicator
-/
lemma indepSets_comap_of_bcf
    {𝒜 : Set (Set Ω)} (m𝒜 : forall A in 𝒜, NullMeasurableSet A P) (mZ : AEMeasurable Z P)
    (h : forall A in 𝒜, forall f : G ->ᵇ Real, ∫ ω in A, f (Z ω) ∂P = P.real A * ∫ ω, f (Z ω) ∂P) :
    IndepSets 𝒜 {A | MeasurableSet[MeasurableSpace.comap Z inferInstance] A} P :=
  indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_of_bcf (m𝒜 A hA) mZ (h A hA))

end IndepSets

section Indep

/--
lemma `indep_comap_pi_of_prod_bcf` / 引理 `indep_comap_pi_of_prod_bcf`

English:
lemma indep_comap_pi_of_prod_bcf
  statement: (hm : m <= mΩ) (mX : forall s, AEMeasurable (X s) P)
  proof: (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_pi_of_prod_bcf (fun A hA => (hm A hA).nullMeasurableSet) mX h)

omit [Fintype S] in variable [Finite S] in

中文:
引理 indep_comap_pi_of_prod_bcf
  结论: (hm : m <= mΩ) (mX : 对任意 s, 几乎处处可测 (X s) P)
  证明: (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_pi_of_prod_bcf (fun A hA => (hm A hA).nullMeasurableSet) mX h)

omit [Fintype S] in variable [Finite S] in

Depends on / 依赖: Indep_iff_IndepSets, indepSets_comap_pi_of_prod_bcf, nullMeasurableSet
-/
lemma indep_comap_pi_of_prod_bcf (hm : m <= mΩ) (mX : forall s, AEMeasurable (X s) P)
    (h : forall A, MeasurableSet[m] A -> forall f : (s : S) -> E s ->ᵇ Real,
      ∫ ω in A, ∏ s, f s (X s ω) ∂P = P.real A * ∫ ω, ∏ s, f s (X s ω) ∂P) :
    Indep m (MeasurableSpace.pi.comap (fun ω s => X s ω)) P :=
  (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_pi_of_prod_bcf (fun A hA => (hm A hA).nullMeasurableSet) mX h)

omit [Fintype S] in variable [Finite S] in
/--
lemma `indep_comap_pi_of_bcf` / 引理 `indep_comap_pi_of_bcf`

English:
lemma indep_comap_pi_of_bcf
  statement: (hm : m <= mΩ) (mX : forall s, AEMeasurable (X s) P)
  proof: (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_pi_of_bcf (fun A hA => (hm A hA).nullMeasurableSet) mX h)

中文:
引理 indep_comap_pi_of_bcf
  结论: (hm : m <= mΩ) (mX : 对任意 s, 几乎处处可测 (X s) P)
  证明: (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_pi_of_bcf (fun A hA => (hm A hA).nullMeasurableSet) mX h)

Depends on / 依赖: Indep_iff_IndepSets, indepSets_comap_pi_of_bcf, nullMeasurableSet
-/
lemma indep_comap_pi_of_bcf (hm : m <= mΩ) (mX : forall s, AEMeasurable (X s) P)
    (h : forall A, MeasurableSet[m] A -> forall f : (Π s, E s) ->ᵇ Real,
      ∫ ω in A, f (X · ω) ∂P = P.real A * ∫ ω, f (X · ω) ∂P) :
    Indep m (MeasurableSpace.pi.comap (fun ω s => X s ω)) P :=
  (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_pi_of_bcf (fun A hA => (hm A hA).nullMeasurableSet) mX h)

/--
lemma `indep_comap_of_bcf` / 引理 `indep_comap_of_bcf`

English:
lemma indep_comap_of_bcf
  statement: (hm : m <= mΩ) (mZ : AEMeasurable Z P)
  proof: (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_of_bcf (fun A hA => (hm A hA).nullMeasurableSet) mZ h)

中文:
引理 indep_comap_of_bcf
  结论: (hm : m <= mΩ) (mZ : 几乎处处可测 Z P)
  证明: (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_of_bcf (fun A hA => (hm A hA).nullMeasurableSet) mZ h)

Depends on / 依赖: Indep_iff_IndepSets, indepSets_comap_of_bcf, nullMeasurableSet
-/
lemma indep_comap_of_bcf (hm : m <= mΩ) (mZ : AEMeasurable Z P)
    (h : forall A, MeasurableSet[m] A -> forall f : G ->ᵇ Real,
      ∫ ω in A, f (Z ω) ∂P = P.real A * ∫ ω, f (Z ω) ∂P) :
    Indep m (MeasurableSpace.comap Z inferInstance) P :=
  (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_of_bcf (fun A hA => (hm A hA).nullMeasurableSet) mZ h)

end Indep

end Fintype

section Process

section IndepFun

variable [IsZeroOrProbabilityMeasure P]

/--
lemma `process_indepFun_process_of_prod_bcf` / 引理 `process_indepFun_process_of_prod_bcf`

English:
lemma process_indepFun_process_of_prod_bcf
  proof: IndepFun.process_indepFun_process₀ mX mY
    fun I J => pi_indepFun_pi_of_prod_bcf (by fun_prop) (by fun_prop) (h I J)

中文:
引理 process_indepFun_process_of_prod_bcf
  证明: IndepFun.process_indepFun_process₀ mX mY
    fun I J => pi_indepFun_pi_of_prod_bcf (by fun_prop) (by fun_prop) (h I J)

Depends on / 依赖: IndepFun, IndepFun.process_indepFun_process, fun_prop, pi_indepFun_pi_of_prod_bcf
-/
lemma process_indepFun_process_of_prod_bcf
    (mX : forall s, AEMeasurable (X s) P) (mY : forall t, AEMeasurable (Y t) P)
    (h : forall (I : Finset S) (J : Finset T) (f : (s : I) -> E s ->ᵇ Real) (g : (t : J) -> F t ->ᵇ Real),
      P[(∏ s, f s ∘ (X s)) * (∏ t, g t ∘ (Y t))] = P[∏ s, f s ∘ (X s)] * P[∏ t, g t ∘ (Y t)]) :
    IndepFun (fun ω s => X s ω) (fun ω t => Y t ω) P :=
  IndepFun.process_indepFun_process₀ mX mY
    fun I J => pi_indepFun_pi_of_prod_bcf (by fun_prop) (by fun_prop) (h I J)

/--
lemma `process_indepFun_process_of_bcf` / 引理 `process_indepFun_process_of_bcf`

English:
lemma process_indepFun_process_of_bcf
  proof: IndepFun.process_indepFun_process₀ mX mY
    fun I J => pi_indepFun_pi_of_bcf (by fun_prop) (by fun_prop) (h I J)

中文:
引理 process_indepFun_process_of_bcf
  证明: IndepFun.process_indepFun_process₀ mX mY
    fun I J => pi_indepFun_pi_of_bcf (by fun_prop) (by fun_prop) (h I J)

Depends on / 依赖: IndepFun, IndepFun.process_indepFun_process, fun_prop, pi_indepFun_pi_of_bcf
-/
lemma process_indepFun_process_of_bcf
    (mX : forall s, AEMeasurable (X s) P) (mY : forall t, AEMeasurable (Y t) P)
    (h : forall (I : Finset S) (J : Finset T) (f : (Π s : I, E s) ->ᵇ Real) (g : (Π t : J, F t) ->ᵇ Real),
      P[fun ω => f (X · ω) * g (Y · ω)] = P[fun ω => f (X · ω)] * P[fun ω => g (Y · ω)]) :
    IndepFun (fun ω s => X s ω) (fun ω t => Y t ω) P :=
  IndepFun.process_indepFun_process₀ mX mY
    fun I J => pi_indepFun_pi_of_bcf (by fun_prop) (by fun_prop) (h I J)

/--
lemma `indepFun_process_of_prod_bcf` / 引理 `indepFun_process_of_prod_bcf`

English:
lemma indepFun_process_of_prod_bcf
  proof: IndepFun.indepFun_process₀ mZ mY fun J =>
    indepFun_pi_of_prod_bcf (by fun_prop) (by fun_prop) (h · J)

中文:
引理 indepFun_process_of_prod_bcf
  证明: IndepFun.indepFun_process₀ mZ mY fun J =>
    indepFun_pi_of_prod_bcf (by fun_prop) (by fun_prop) (h · J)

Depends on / 依赖: IndepFun, IndepFun.indepFun_process, fun_prop, indepFun_pi_of_prod_bcf
-/
lemma indepFun_process_of_prod_bcf
    (mZ : AEMeasurable Z P) (mY : forall t, AEMeasurable (Y t) P)
    (h : forall (f : G ->ᵇ Real) (J : Finset T) (g : (t : J) -> F t ->ᵇ Real),
      P[f ∘ Z * (∏ t, g t ∘ (Y t))] = P[f ∘ Z] * P[∏ t, g t ∘ (Y t)]) :
    IndepFun Z (fun ω t => Y t ω) P :=
  IndepFun.indepFun_process₀ mZ mY fun J =>
    indepFun_pi_of_prod_bcf (by fun_prop) (by fun_prop) (h · J)

/--
lemma `indepFun_process_of_bcf` / 引理 `indepFun_process_of_bcf`

English:
lemma indepFun_process_of_bcf
  proof: IndepFun.indepFun_process₀ mZ mY fun J => indepFun_pi_of_bcf (by fun_prop) (by fun_prop) (h · J)

中文:
引理 indepFun_process_of_bcf
  证明: IndepFun.indepFun_process₀ mZ mY fun J => indepFun_pi_of_bcf (by fun_prop) (by fun_prop) (h · J)

Depends on / 依赖: IndepFun, IndepFun.indepFun_process, fun_prop, indepFun_pi_of_bcf
-/
lemma indepFun_process_of_bcf
    (mZ : AEMeasurable Z P) (mY : forall t, AEMeasurable (Y t) P)
    (h : forall (f : G ->ᵇ Real) (J : Finset T) (g : (Π t : J, F t) ->ᵇ Real),
      P[fun ω => f (Z ω) * g (Y · ω)] = P[f ∘ Z] * P[fun ω => g (Y · ω)]) :
    IndepFun Z (fun ω t => Y t ω) P :=
  IndepFun.indepFun_process₀ mZ mY fun J => indepFun_pi_of_bcf (by fun_prop) (by fun_prop) (h · J)

/--
lemma `process_indepFun_of_prod_bcf` / 引理 `process_indepFun_of_prod_bcf`

English:
lemma process_indepFun_of_prod_bcf
  proof: IndepFun.process_indepFun₀ mX mU fun I => pi_indepFun_of_prod_bcf (by fun_prop) (by fun_prop) (h I)

中文:
引理 process_indepFun_of_prod_bcf
  证明: IndepFun.process_indepFun₀ mX mU fun I => pi_indepFun_of_prod_bcf (by fun_prop) (by fun_prop) (h I)

Depends on / 依赖: IndepFun, IndepFun.process_indepFun, fun_prop, pi_indepFun_of_prod_bcf
-/
lemma process_indepFun_of_prod_bcf
    (mX : forall s, AEMeasurable (X s) P) (mU : AEMeasurable U P)
    (h : forall (I : Finset S) (f : (s : I) -> E s ->ᵇ Real) (g : H ->ᵇ Real),
      P[(∏ s, f s ∘ (X s)) * g ∘ U] = P[∏ s, f s ∘ (X s)] * P[g ∘ U]) :
    IndepFun (fun ω s => X s ω) U P :=
  IndepFun.process_indepFun₀ mX mU fun I => pi_indepFun_of_prod_bcf (by fun_prop) (by fun_prop) (h I)

/--
lemma `process_indepFun_of_bcf` / 引理 `process_indepFun_of_bcf`

English:
lemma process_indepFun_of_bcf
  proof: IndepFun.process_indepFun₀ mX mU fun I => pi_indepFun_of_bcf (by fun_prop) (by fun_prop) (h I)

中文:
引理 process_indepFun_of_bcf
  证明: IndepFun.process_indepFun₀ mX mU fun I => pi_indepFun_of_bcf (by fun_prop) (by fun_prop) (h I)

Depends on / 依赖: IndepFun, IndepFun.process_indepFun, fun_prop, pi_indepFun_of_bcf
-/
lemma process_indepFun_of_bcf
    (mX : forall s, AEMeasurable (X s) P) (mU : AEMeasurable U P)
    (h : forall (I : Finset S) (f : (Π s : I, E s) ->ᵇ Real) (g : H ->ᵇ Real),
      P[fun ω => f (X · ω) * g (U ω)] = P[fun ω => f (X · ω)] * P[g ∘ U]) :
    IndepFun (fun ω s => X s ω) U P :=
  IndepFun.process_indepFun₀ mX mU fun I => pi_indepFun_of_bcf (by fun_prop) (by fun_prop) (h I)

end IndepFun

variable [IsProbabilityMeasure P]

section Indicator

/--
lemma `indicator_indepFun_process_of_prod_bcf` / 引理 `indicator_indepFun_process_of_prod_bcf`

English:
lemma indicator_indepFun_process_of_prod_bcf
  proof: IndepFun.indepFun_process₀ ((aemeasurable_indicator_const_iff 1).2 mA) mX
    fun I => indicator_indepFun_pi_of_prod_bcf mA (by fun_prop) (h I)

中文:
引理 indicator_indepFun_process_of_prod_bcf
  证明: IndepFun.indepFun_process₀ ((aemeasurable_indicator_const_iff 1).2 mA) mX
    fun I => indicator_indepFun_pi_of_prod_bcf mA (by fun_prop) (h I)

Depends on / 依赖: IndepFun, IndepFun.indepFun_process, aemeasurable_indicator_const_iff, fun_prop, indicator_indepFun_pi_of_prod_bcf
-/
lemma indicator_indepFun_process_of_prod_bcf
    {A : Set Ω} (mA : NullMeasurableSet A P) (mX : forall s, AEMeasurable (X s) P)
    (h : forall (I : Finset S) (f : (s : I) -> E s ->ᵇ Real),
      ∫ ω in A, ∏ s, f s (X s ω) ∂P = P.real A * ∫ ω, ∏ s, f s (X s ω) ∂P) :
    IndepFun (A.indicator (1 : Ω -> Real)) (fun ω s => X s ω) P :=
  IndepFun.indepFun_process₀ ((aemeasurable_indicator_const_iff 1).2 mA) mX
    fun I => indicator_indepFun_pi_of_prod_bcf mA (by fun_prop) (h I)

/--
lemma `indicator_indepFun_process_of_bcf` / 引理 `indicator_indepFun_process_of_bcf`

English:
lemma indicator_indepFun_process_of_bcf
  proof: IndepFun.indepFun_process₀ ((aemeasurable_indicator_const_iff 1).2 mA) mX
    fun I => indicator_indepFun_pi_of_bcf mA (by fun_prop) (h I)

中文:
引理 indicator_indepFun_process_of_bcf
  证明: IndepFun.indepFun_process₀ ((aemeasurable_indicator_const_iff 1).2 mA) mX
    fun I => indicator_indepFun_pi_of_bcf mA (by fun_prop) (h I)

Depends on / 依赖: IndepFun, IndepFun.indepFun_process, aemeasurable_indicator_const_iff, fun_prop, indicator_indepFun_pi_of_bcf
-/
lemma indicator_indepFun_process_of_bcf
    {A : Set Ω} (mA : NullMeasurableSet A P) (mX : forall s, AEMeasurable (X s) P)
    (h : forall (I : Finset S) (f : (Π s : I, E s) ->ᵇ Real),
      ∫ ω in A, f (X · ω) ∂P = P.real A * ∫ ω, f (X · ω) ∂P) :
    IndepFun (A.indicator (1 : Ω -> Real)) (fun ω s => X s ω) P :=
  IndepFun.indepFun_process₀ ((aemeasurable_indicator_const_iff 1).2 mA) mX
    fun I => indicator_indepFun_pi_of_bcf mA (by fun_prop) (h I)

end Indicator

section IndepSets

/--
lemma `indepSets_comap_process_of_prod_bcf` / 引理 `indepSets_comap_process_of_prod_bcf`

English:
lemma indepSets_comap_process_of_prod_bcf
  proof: indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_process_of_prod_bcf (m𝒜 A hA) mX (h A hA))

中文:
引理 indepSets_comap_process_of_prod_bcf
  证明: indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_process_of_prod_bcf (m𝒜 A hA) mX (h A hA))

Depends on / 依赖: IndepFun, IndepFun.singleton_indepSets_of_indicator, indepSets_iff_singleton_indepSets, indicator_indepFun_process_of_prod_bcf, singleton_indepSets_of_indicator
-/
lemma indepSets_comap_process_of_prod_bcf
    {𝒜 : Set (Set Ω)} (m𝒜 : forall A in 𝒜, NullMeasurableSet A P) (mX : forall s, AEMeasurable (X s) P)
    (h : forall A in 𝒜, forall (I : Finset S) (f : (s : I) -> E s ->ᵇ Real),
      ∫ ω in A, ∏ s, f s (X s ω) ∂P = P.real A * ∫ ω, ∏ s, f s (X s ω) ∂P) :
    IndepSets 𝒜 {A | MeasurableSet[MeasurableSpace.pi.comap (fun ω s => X s ω)] A} P :=
  indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_process_of_prod_bcf (m𝒜 A hA) mX (h A hA))

/--
lemma `indepSets_comap_process_of_bcf` / 引理 `indepSets_comap_process_of_bcf`

English:
lemma indepSets_comap_process_of_bcf
  proof: indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_process_of_bcf (m𝒜 A hA) mX (h A hA))

中文:
引理 indepSets_comap_process_of_bcf
  证明: indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_process_of_bcf (m𝒜 A hA) mX (h A hA))

Depends on / 依赖: IndepFun, IndepFun.singleton_indepSets_of_indicator, indepSets_iff_singleton_indepSets, indicator_indepFun_process_of_bcf, singleton_indepSets_of_indicator
-/
lemma indepSets_comap_process_of_bcf
    {𝒜 : Set (Set Ω)} (m𝒜 : forall A in 𝒜, NullMeasurableSet A P) (mX : forall s, AEMeasurable (X s) P)
    (h : forall A in 𝒜, forall (I : Finset S) (f : (Π s : I, E s) ->ᵇ Real),
      ∫ ω in A, f (X · ω) ∂P = P.real A * ∫ ω, f (X · ω) ∂P) :
    IndepSets 𝒜 {A | MeasurableSet[MeasurableSpace.pi.comap (fun ω s => X s ω)] A} P :=
  indepSets_iff_singleton_indepSets.2 fun A hA => IndepFun.singleton_indepSets_of_indicator
    (indicator_indepFun_process_of_bcf (m𝒜 A hA) mX (h A hA))

end IndepSets

section Indep

/--
lemma `indep_comap_process_of_prod_bcf` / 引理 `indep_comap_process_of_prod_bcf`

English:
lemma indep_comap_process_of_prod_bcf
  proof: (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_process_of_prod_bcf (fun A hA => (hm A hA).nullMeasurableSet) mX h)

中文:
引理 indep_comap_process_of_prod_bcf
  证明: (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_process_of_prod_bcf (fun A hA => (hm A hA).nullMeasurableSet) mX h)

Depends on / 依赖: Indep_iff_IndepSets, indepSets_comap_process_of_prod_bcf, nullMeasurableSet
-/
lemma indep_comap_process_of_prod_bcf
    (hm : m <= mΩ) (mX : forall s, AEMeasurable (X s) P)
    (h : forall A, MeasurableSet[m] A -> forall (I : Finset S) (f : (s : I) -> E s ->ᵇ Real),
      ∫ ω in A, ∏ s, f s (X s ω) ∂P = P.real A * ∫ ω, ∏ s, f s (X s ω) ∂P) :
    Indep m (MeasurableSpace.pi.comap (fun ω s => X s ω)) P :=
  (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_process_of_prod_bcf (fun A hA => (hm A hA).nullMeasurableSet) mX h)

/--
lemma `indep_comap_process_of_bcf` / 引理 `indep_comap_process_of_bcf`

English:
lemma indep_comap_process_of_bcf
  proof: (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_process_of_bcf (fun A hA => (hm A hA).nullMeasurableSet) mX h)

中文:
引理 indep_comap_process_of_bcf
  证明: (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_process_of_bcf (fun A hA => (hm A hA).nullMeasurableSet) mX h)

Depends on / 依赖: Indep_iff_IndepSets, indepSets_comap_process_of_bcf, nullMeasurableSet
-/
lemma indep_comap_process_of_bcf
    (hm : m <= mΩ) (mX : forall s, AEMeasurable (X s) P)
    (h : forall A, MeasurableSet[m] A -> forall (I : Finset S) (f : (Π s : I, E s) ->ᵇ Real),
      ∫ ω in A, f (X · ω) ∂P = P.real A * ∫ ω, f (X · ω) ∂P) :
    Indep m (MeasurableSpace.pi.comap (fun ω s => X s ω)) P :=
  (Indep_iff_IndepSets _ _ P).2
    (indepSets_comap_process_of_bcf (fun A hA => (hm A hA).nullMeasurableSet) mX h)

end Indep

end Process
