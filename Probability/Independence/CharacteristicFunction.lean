/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Links between independence and characteristic function

Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. More specifically, prove this in Hilbert spaces for
two variables and a finite family of variables. We prove the analogous statements in Banach spaces,
with an arbitrary Lp norm, for the dual characteristic function.
-/

public section

namespace ProbabilityTheory

open MeasureTheory WithLp Finset
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  (p : Real>=0∞) [Fact (1 <= p)]

section IndepFun

variable [IsFiniteMeasure P] {E F : Type*}
  {mE : MeasurableSpace E} [NormedAddCommGroup E]
  [BorelSpace E] [SecondCountableTopology E]
  {mF : MeasurableSpace F} [NormedAddCommGroup F] [CompleteSpace F]
  [BorelSpace F] [SecondCountableTopology F]
  {X : Ω -> E} {Y : Ω -> F}

section InnerProductSpace

variable [InnerProductSpace Real E] [InnerProductSpace Real F]

/--
lemma `IndepFun.charFun_map_add_eq_mul` / 引理 `IndepFun.charFun_map_add_eq_mul`

English:
lemma IndepFun.charFun_map_add_eq_mul
  statement: {Y : Ω -> E}
  proof: by
  ext t
  rw [hXY.map_add_eq_map_conv_map₀ mX mY]; rw [charFun_conv]; rw [Pi.mul_apply]

中文:
引理 IndepFun.charFun_map_add_eq_mul
  结论: {Y : Ω -> E}
  证明: by
  ext t
  rw [hXY.map_add_eq_map_conv_map₀ mX mY]; rw [charFun_conv]; rw [Pi.mul_apply]

Depends on / 依赖: Pi.mul_apply, charFun_conv, hXY.map_add_eq_map_conv_map, mul_apply
-/
lemma IndepFun.charFun_map_add_eq_mul {Y : Ω -> E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y) :
    charFun (P.map (X + Y)) = charFun (P.map X) * charFun (P.map Y) := by
  ext t
  rw [hXY.map_add_eq_map_conv_map₀ mX mY]; rw [charFun_conv]; rw [Pi.mul_apply]

/--
lemma `IndepFun.charFun_map_fun_add_eq_mul` / 引理 `IndepFun.charFun_map_fun_add_eq_mul`

English:
lemma IndepFun.charFun_map_fun_add_eq_mul
  statement: {Y : Ω -> E}
  proof: hXY.charFun_map_add_eq_mul mX mY

中文:
引理 IndepFun.charFun_map_fun_add_eq_mul
  结论: {Y : Ω -> E}
  证明: hXY.charFun_map_add_eq_mul mX mY

Depends on / 依赖: charFun_map_add_eq_mul, hXY.charFun_map_add_eq_mul
-/
lemma IndepFun.charFun_map_fun_add_eq_mul {Y : Ω -> E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y) :
    charFun (P.map (fun ω => X ω + Y ω)) = charFun (P.map X) * charFun (P.map Y) :=
  hXY.charFun_map_add_eq_mul mX mY

/--
lemma `charFun_map_add_prod_eq_mul` / 引理 `charFun_map_add_prod_eq_mul`

English:
lemma charFun_map_add_prod_eq_mul
  statement: {μ ν : Measure E}
  proof: by
  rw [IndepFun.charFun_map_fun_add_eq_mul]; rw [measurePreserving_fst.map_eq]; rw [measurePreserving_snd.map_eq]
  any_goals fun_prop
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

中文:
引理 charFun_map_add_prod_eq_mul
  结论: {μ ν : Measure E}
  证明: by
  rw [IndepFun.charFun_map_fun_add_eq_mul]; rw [measurePreserving_fst.map_eq]; rw [measurePreserving_snd.map_eq]
  any_goals fun_prop
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

Depends on / 依赖: IndepFun, IndepFun.charFun_map_fun_add_eq_mul, any_goals, charFun_map_fun_add_eq_mul, fun_prop, indepFun_prod, map_eq, measurable_id, measurePreserving_fst, measurePreserving_fst.map_eq, measurePreserving_snd, measurePreserving_snd.map_eq
-/
lemma charFun_map_add_prod_eq_mul {μ ν : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    charFun ((μ.prod ν).map (fun p => p.1 + p.2)) = charFun μ * charFun ν := by
  rw [IndepFun.charFun_map_fun_add_eq_mul]; rw [measurePreserving_fst.map_eq]; rw [measurePreserving_snd.map_eq]
  any_goals fun_prop
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

/--
lemma `indepFun_iff_charFun_prod` / 引理 `indepFun_iff_charFun_prod`

English:
lemma indepFun_iff_charFun_prod
  given: [CompleteSpace E] (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
  proof: by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY]; rw [← charFun_eq_prod_iff]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]; rw [Function.comp_def]

中文:
引理 indepFun_iff_charFun_prod
  条件: [CompleteSpace E] (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
  证明: by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY]; rw [← charFun_eq_prod_iff]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]; rw [Function.comp_def]

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, Function, Function.comp_def, charFun_eq_prod_iff, comp_def, fun_prop, indepFun_iff_map_prod_eq_prod_map_map, map_map_of_aemeasurable
-/
lemma indepFun_iff_charFun_prod [CompleteSpace E] (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    X ⟂ᵢ[P] Y ↔ forall t, charFun (P.map (fun ω => toLp 2 (X ω, Y ω))) t =
      charFun (P.map X) t.ofLp.1 * charFun (P.map Y) t.ofLp.2 := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY]; rw [← charFun_eq_prod_iff]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]; rw [Function.comp_def]

end InnerProductSpace

section NormedSpace

variable [NormedSpace Real E] [NormedSpace Real F]

/--
lemma `IndepFun.charFunDual_map_add_eq_mul` / 引理 `IndepFun.charFunDual_map_add_eq_mul`

English:
lemma IndepFun.charFunDual_map_add_eq_mul
  statement: {Y : Ω -> E}
  proof: by
  ext L
  rw [hXY.map_add_eq_map_conv_map₀ mX mY]; rw [charFunDual_conv]; rw [Pi.mul_apply]

中文:
引理 IndepFun.charFunDual_map_add_eq_mul
  结论: {Y : Ω -> E}
  证明: by
  ext L
  rw [hXY.map_add_eq_map_conv_map₀ mX mY]; rw [charFunDual_conv]; rw [Pi.mul_apply]

Depends on / 依赖: Pi.mul_apply, charFunDual_conv, hXY.map_add_eq_map_conv_map, mul_apply
-/
lemma IndepFun.charFunDual_map_add_eq_mul {Y : Ω -> E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y) :
    charFunDual (P.map (X + Y)) = charFunDual (P.map X) * charFunDual (P.map Y) := by
  ext L
  rw [hXY.map_add_eq_map_conv_map₀ mX mY]; rw [charFunDual_conv]; rw [Pi.mul_apply]

/--
lemma `IndepFun.charFunDual_map_fun_add_eq_mul` / 引理 `IndepFun.charFunDual_map_fun_add_eq_mul`

English:
lemma IndepFun.charFunDual_map_fun_add_eq_mul
  statement: {Y : Ω -> E}
  proof: hXY.charFunDual_map_add_eq_mul mX mY

中文:
引理 IndepFun.charFunDual_map_fun_add_eq_mul
  结论: {Y : Ω -> E}
  证明: hXY.charFunDual_map_add_eq_mul mX mY

Depends on / 依赖: charFunDual_map_add_eq_mul, hXY.charFunDual_map_add_eq_mul
-/
lemma IndepFun.charFunDual_map_fun_add_eq_mul {Y : Ω -> E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y) :
    charFunDual (P.map (fun ω => X ω + Y ω)) = charFunDual (P.map X) * charFunDual (P.map Y) :=
  hXY.charFunDual_map_add_eq_mul mX mY

/--
lemma `charFunDual_map_add_prod_eq_mul` / 引理 `charFunDual_map_add_prod_eq_mul`

English:
lemma charFunDual_map_add_prod_eq_mul
  statement: {μ ν : Measure E}
  proof: by
  rw [IndepFun.charFunDual_map_fun_add_eq_mul]; rw [measurePreserving_fst.map_eq]; rw [measurePreserving_snd.map_eq]
  any_goals fun_prop
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

中文:
引理 charFunDual_map_add_prod_eq_mul
  结论: {μ ν : Measure E}
  证明: by
  rw [IndepFun.charFunDual_map_fun_add_eq_mul]; rw [measurePreserving_fst.map_eq]; rw [measurePreserving_snd.map_eq]
  any_goals fun_prop
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

Depends on / 依赖: IndepFun, IndepFun.charFunDual_map_fun_add_eq_mul, any_goals, charFunDual_map_fun_add_eq_mul, fun_prop, indepFun_prod, map_eq, measurable_id, measurePreserving_fst, measurePreserving_fst.map_eq, measurePreserving_snd, measurePreserving_snd.map_eq
-/
lemma charFunDual_map_add_prod_eq_mul {μ ν : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    charFunDual ((μ.prod ν).map (fun p => p.1 + p.2)) = charFunDual μ * charFunDual ν := by
  rw [IndepFun.charFunDual_map_fun_add_eq_mul]; rw [measurePreserving_fst.map_eq]; rw [measurePreserving_snd.map_eq]
  any_goals fun_prop
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

variable [CompleteSpace E]

/--
lemma `indepFun_iff_charFunDual_prod` / 引理 `indepFun_iff_charFunDual_prod`

English:
lemma indepFun_iff_charFunDual_prod
  given: (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
  proof: by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY]; rw [← charFunDual_eq_prod_iff]

中文:
引理 indepFun_iff_charFunDual_prod
  条件: (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
  证明: by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY]; rw [← charFunDual_eq_prod_iff]

Depends on / 依赖: charFunDual_eq_prod_iff, indepFun_iff_map_prod_eq_prod_map_map
-/
lemma indepFun_iff_charFunDual_prod (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    X ⟂ᵢ[P] Y ↔ forall L, charFunDual (P.map (fun ω => (X ω, Y ω))) L =
      charFunDual (P.map X) (L.comp (.inl Real E F)) *
      charFunDual (P.map Y) (L.comp (.inr Real E F)) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY]; rw [← charFunDual_eq_prod_iff]

/--
lemma `indepFun_iff_charFunDual_prod'` / 引理 `indepFun_iff_charFunDual_prod'`

English:
lemma indepFun_iff_charFunDual_prod'
  given: (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
  proof: by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY]; rw [← charFunDual_eq_prod_iff' p]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]; rw [Function.comp_def]

中文:
引理 indepFun_iff_charFunDual_prod'
  条件: (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
  证明: by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY]; rw [← charFunDual_eq_prod_iff' p]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]; rw [Function.comp_def]

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, Function, Function.comp_def, charFunDual_eq_prod_iff, comp_def, fun_prop, indepFun_iff_map_prod_eq_prod_map_map, map_map_of_aemeasurable
-/
lemma indepFun_iff_charFunDual_prod' (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    X ⟂ᵢ[P] Y ↔ forall L, charFunDual (P.map (fun ω => toLp p (X ω, Y ω))) L =
      charFunDual (P.map X) (L.comp
        ((prodContinuousLinearEquiv p Real E F).symm.toContinuousLinearMap.comp
          (.inl Real E F))) *
      charFunDual (P.map Y) (L.comp
        ((prodContinuousLinearEquiv p Real E F).symm.toContinuousLinearMap.comp
          (.inr Real E F))) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY]; rw [← charFunDual_eq_prod_iff' p]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]; rw [Function.comp_def]

end NormedSpace

end IndepFun

section iIndepFun

variable {ι : Type*} {s : Finset ι}

section Sum

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E] [SecondCountableTopology E] {X : ι -> Ω -> E}

/--
lemma `iIndepFun.charFunDual_map_finsetSum_eq_prod` / 引理 `iIndepFun.charFunDual_map_finsetSum_eq_prod`

English:
lemma iIndepFun.charFunDual_map_finsetSum_eq_prod
  statement: [NormedSpace Real E]
  proof: by
  classical
  have := hX.isProbabilityMeasure
  induction s using Finset.induction with
  | empty => ext; simp [show (0 : Ω -> E) = fun _ => 0 from rfl]
  | insert i s hi hs =>
    rw [Finset.sum_insert hi]; rw [IndepFun.charFunDual_map_add_eq_mul]; rw [Finset.prod_insert hi]; rw [hs]
    · exact

中文:
引理 iIndepFun.charFunDual_map_finsetSum_eq_prod
  结论: [NormedSpace 实数 E]
  证明: by
  classical
  have := hX.isProbabilityMeasure
  induction s using Finset.induction with
  | empty => ext; simp [show (0 : Ω -> E) = fun _ => 0 from rfl]
  | insert i s hi hs =>
    rw [Finset.sum_insert hi]; rw [IndepFun.charFunDual_map_add_eq_mul]; rw [Finset.prod_insert hi]; rw [hs]
    · exact

Depends on / 依赖: Finset, Finset.aemeasurable_sum, Finset.induction, Finset.prod_insert, Finset.sum_insert, IndepFun, IndepFun.charFunDual_map_add_eq_mul, aemeasurable_sum, charFunDual_map_add_eq_mul, classical, hX.isProbabilityMeasure, hX.precomp, insert, isProbabilityMeasure, mem_insert_of_mem, mem_insert_self, precomp, prod_insert, sum_insert
-/
lemma iIndepFun.charFunDual_map_finsetSum_eq_prod [NormedSpace Real E]
    (mX : forall i in s, AEMeasurable (X i) P) (hX : iIndepFun (s.restrict X) P) :
    charFunDual (P.map (∑ i in s, X i)) = ∏ i in s, charFunDual (P.map (X i)) := by
  classical
  have := hX.isProbabilityMeasure
  induction s using Finset.induction with
  | empty => ext; simp [show (0 : Ω -> E) = fun _ => 0 from rfl]
  | insert i s hi hs =>
    rw [Finset.sum_insert hi]; rw [IndepFun.charFunDual_map_add_eq_mul]; rw [Finset.prod_insert hi]; rw [hs]
    · exact fun i hi => (mX i (mem_insert_of_mem hi))
    · exact hX.precomp (g := fun x : s => ⟨x.1, mem_insert_of_mem x.2⟩) (fun _ => by simp)
    · exact mX i (mem_insert_self i s)
    · exact Finset.aemeasurable_sum s (fun i hi => (mX i (mem_insert_of_mem hi)))
    symm
    convert!
      iIndepFun.indepFun_finsetSum_of_notMem₀ (i := ⟨i, mem_insert_self i s⟩) (f :=
        fun (x : (insert i s : Finset ι)) => X x.1) (s := {x | x.1 in s}) hX (fun i => (mX i.1 i.2))
        (by simpa)
    let e : ((insert i s) : Finset ι) -> ι := Subtype.val
    convert! (Finset.sum_of_injOn Subtype.val ?_ ?_ ?_ ?_).symm
    · simp
    · intro _ _; grind
    · simp; grind
    · grind

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFunDual_map_finset_sum_eq_prod := iIndepFun.charFunDual_map_finsetSum_eq_prod

/--
lemma `iIndepFun.charFunDual_map_sum_eq_prod` / 引理 `iIndepFun.charFunDual_map_sum_eq_prod`

English:
lemma iIndepFun.charFunDual_map_sum_eq_prod
  statement: [Fintype ι] [NormedSpace Real E]
  proof: (hX.restrict _).charFunDual_map_finsetSum_eq_prod (by simpa)

中文:
引理 iIndepFun.charFunDual_map_sum_eq_prod
  结论: [Fintype ι] [NormedSpace 实数 E]
  证明: (hX.restrict _).charFunDual_map_finsetSum_eq_prod (by simpa)

Depends on / 依赖: charFunDual_map_finsetSum_eq_prod, hX.restrict, restrict
-/
lemma iIndepFun.charFunDual_map_sum_eq_prod [Fintype ι] [NormedSpace Real E]
    (mX : forall i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFunDual (P.map (∑ i, X i)) = ∏ i, charFunDual (P.map (X i)) :=
  (hX.restrict _).charFunDual_map_finsetSum_eq_prod (by simpa)

/--
lemma `iIndepFun.charFunDual_map_fun_finsetSum_eq_prod` / 引理 `iIndepFun.charFunDual_map_fun_finsetSum_eq_prod`

English:
lemma iIndepFun.charFunDual_map_fun_finsetSum_eq_prod
  statement: [NormedSpace Real E]
  proof: by
  convert! hX.charFunDual_map_finsetSum_eq_prod mX
  simp

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFunDual_map_fun_finset_sum_eq_prod :=
  iIndepFun.charFunDual_map_fun_finsetSum_eq_prod

中文:
引理 iIndepFun.charFunDual_map_fun_finsetSum_eq_prod
  结论: [NormedSpace 实数 E]
  证明: by
  convert! hX.charFunDual_map_finsetSum_eq_prod mX
  simp

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFunDual_map_fun_finset_sum_eq_prod :=
  iIndepFun.charFunDual_map_fun_finsetSum_eq_prod

Depends on / 依赖: charFunDual_map_finsetSum_eq_prod, convert, hX.charFunDual_map_finsetSum_eq_prod
-/
lemma iIndepFun.charFunDual_map_fun_finsetSum_eq_prod [NormedSpace Real E]
    (mX : forall i in s, AEMeasurable (X i) P) (hX : iIndepFun (s.restrict X) P) :
    charFunDual (P.map (fun ω => ∑ i in s, X i ω)) = ∏ i in s, charFunDual (P.map (X i)) := by
  convert! hX.charFunDual_map_finsetSum_eq_prod mX
  simp

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFunDual_map_fun_finset_sum_eq_prod :=
  iIndepFun.charFunDual_map_fun_finsetSum_eq_prod

/--
lemma `iIndepFun.charFunDual_map_fun_sum_eq_prod` / 引理 `iIndepFun.charFunDual_map_fun_sum_eq_prod`

English:
lemma iIndepFun.charFunDual_map_fun_sum_eq_prod
  statement: [Fintype ι] [NormedSpace Real E]
  proof: (hX.restrict _).charFunDual_map_fun_finsetSum_eq_prod (by simpa)

中文:
引理 iIndepFun.charFunDual_map_fun_sum_eq_prod
  结论: [Fintype ι] [NormedSpace 实数 E]
  证明: (hX.restrict _).charFunDual_map_fun_finsetSum_eq_prod (by simpa)

Depends on / 依赖: charFunDual_map_fun_finsetSum_eq_prod, hX.restrict, restrict
-/
lemma iIndepFun.charFunDual_map_fun_sum_eq_prod [Fintype ι] [NormedSpace Real E]
    (mX : forall i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFunDual (P.map (fun ω => ∑ i, X i ω)) = ∏ i, charFunDual (P.map (X i)) :=
  (hX.restrict _).charFunDual_map_fun_finsetSum_eq_prod (by simpa)

/--
lemma `charFunDual_map_sum_pi_eq_prod` / 引理 `charFunDual_map_sum_pi_eq_prod`

English:
lemma charFunDual_map_sum_pi_eq_prod
  statement: [Fintype ι] [NormedSpace Real E] {μ : ι -> Measure E}
  proof: by
  rw [iIndepFun.charFunDual_map_fun_sum_eq_prod]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [(measurePreserving_eval μ i).map_eq]
  · exact aemeasurable_id.eval
  · exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

中文:
引理 charFunDual_map_sum_pi_eq_prod
  结论: [Fintype ι] [NormedSpace 实数 E] {μ : ι -> Measure E}
  证明: by
  rw [iIndepFun.charFunDual_map_fun_sum_eq_prod]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [(measurePreserving_eval μ i).map_eq]
  · exact aemeasurable_id.eval
  · exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

Depends on / 依赖: Finset, Finset.prod_congr, aemeasurable_id, aemeasurable_id.eval, charFunDual_map_fun_sum_eq_prod, iIndepFun, iIndepFun.charFunDual_map_fun_sum_eq_prod, iIndepFun_pi, map_eq, measurePreserving_eval, prod_congr
-/
lemma charFunDual_map_sum_pi_eq_prod [Fintype ι] [NormedSpace Real E] {μ : ι -> Measure E}
    [forall i, IsProbabilityMeasure (μ i)] :
    charFunDual ((Measure.pi μ).map (fun p => ∑ i, p i)) = ∏ i, charFunDual (μ i) := by
  rw [iIndepFun.charFunDual_map_fun_sum_eq_prod]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [(measurePreserving_eval μ i).map_eq]
  · exact aemeasurable_id.eval
  · exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/--
lemma `iIndepFun.charFun_map_finsetSum_eq_prod` / 引理 `iIndepFun.charFun_map_finsetSum_eq_prod`

English:
lemma iIndepFun.charFun_map_finsetSum_eq_prod
  statement: [InnerProductSpace Real E]
  proof: by
  ext
  simp [charFun_eq_charFunDual_toDualMap, hX.charFunDual_map_finsetSum_eq_prod mX]

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFun_map_finset_sum_eq_prod := iIndepFun.charFun_map_finsetSum_eq_prod

中文:
引理 iIndepFun.charFun_map_finsetSum_eq_prod
  结论: [InnerProductSpace 实数 E]
  证明: by
  ext
  simp [charFun_eq_charFunDual_toDualMap, hX.charFunDual_map_finsetSum_eq_prod mX]

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFun_map_finset_sum_eq_prod := iIndepFun.charFun_map_finsetSum_eq_prod

Depends on / 依赖: charFunDual_map_finsetSum_eq_prod, charFun_eq_charFunDual_toDualMap, hX.charFunDual_map_finsetSum_eq_prod
-/
lemma iIndepFun.charFun_map_finsetSum_eq_prod [InnerProductSpace Real E]
    (mX : forall i in s, AEMeasurable (X i) P) (hX : iIndepFun (s.restrict X) P) :
    charFun (P.map (∑ i in s, X i)) = ∏ i in s, charFun (P.map (X i)) := by
  ext
  simp [charFun_eq_charFunDual_toDualMap, hX.charFunDual_map_finsetSum_eq_prod mX]

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFun_map_finset_sum_eq_prod := iIndepFun.charFun_map_finsetSum_eq_prod

/--
lemma `iIndepFun.charFun_map_sum_eq_prod` / 引理 `iIndepFun.charFun_map_sum_eq_prod`

English:
lemma iIndepFun.charFun_map_sum_eq_prod
  statement: [Fintype ι] [InnerProductSpace Real E]
  proof: (hX.restrict _).charFun_map_finsetSum_eq_prod (by simpa)

中文:
引理 iIndepFun.charFun_map_sum_eq_prod
  结论: [Fintype ι] [InnerProductSpace 实数 E]
  证明: (hX.restrict _).charFun_map_finsetSum_eq_prod (by simpa)

Depends on / 依赖: charFun_map_finsetSum_eq_prod, hX.restrict, restrict
-/
lemma iIndepFun.charFun_map_sum_eq_prod [Fintype ι] [InnerProductSpace Real E]
    (mX : forall i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFun (P.map (∑ i, X i)) = ∏ i, charFun (P.map (X i)) :=
  (hX.restrict _).charFun_map_finsetSum_eq_prod (by simpa)

/--
lemma `iIndepFun.charFun_map_fun_finsetSum_eq_prod` / 引理 `iIndepFun.charFun_map_fun_finsetSum_eq_prod`

English:
lemma iIndepFun.charFun_map_fun_finsetSum_eq_prod
  statement: [InnerProductSpace Real E]
  proof: by
  convert! hX.charFun_map_finsetSum_eq_prod mX
  simp

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFun_map_fun_finset_sum_eq_prod := iIndepFun.charFun_map_fun_finsetSum_eq_prod

中文:
引理 iIndepFun.charFun_map_fun_finsetSum_eq_prod
  结论: [InnerProductSpace 实数 E]
  证明: by
  convert! hX.charFun_map_finsetSum_eq_prod mX
  simp

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFun_map_fun_finset_sum_eq_prod := iIndepFun.charFun_map_fun_finsetSum_eq_prod

Depends on / 依赖: charFun_map_finsetSum_eq_prod, convert, hX.charFun_map_finsetSum_eq_prod
-/
lemma iIndepFun.charFun_map_fun_finsetSum_eq_prod [InnerProductSpace Real E]
    (mX : forall i in s, AEMeasurable (X i) P) (hX : iIndepFun (s.restrict X) P) :
    charFun (P.map (fun ω => ∑ i in s, X i ω)) = ∏ i in s, charFun (P.map (X i)) := by
  convert! hX.charFun_map_finsetSum_eq_prod mX
  simp

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFun_map_fun_finset_sum_eq_prod := iIndepFun.charFun_map_fun_finsetSum_eq_prod

/--
lemma `iIndepFun.charFun_map_fun_sum_eq_prod` / 引理 `iIndepFun.charFun_map_fun_sum_eq_prod`

English:
lemma iIndepFun.charFun_map_fun_sum_eq_prod
  statement: [Fintype ι] [InnerProductSpace Real E]
  proof: (hX.restrict _).charFun_map_fun_finsetSum_eq_prod (by simpa)

中文:
引理 iIndepFun.charFun_map_fun_sum_eq_prod
  结论: [Fintype ι] [InnerProductSpace 实数 E]
  证明: (hX.restrict _).charFun_map_fun_finsetSum_eq_prod (by simpa)

Depends on / 依赖: charFun_map_fun_finsetSum_eq_prod, hX.restrict, restrict
-/
lemma iIndepFun.charFun_map_fun_sum_eq_prod [Fintype ι] [InnerProductSpace Real E]
    (mX : forall i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFun (P.map (fun ω => ∑ i, X i ω)) = ∏ i, charFun (P.map (X i)) :=
  (hX.restrict _).charFun_map_fun_finsetSum_eq_prod (by simpa)

/--
lemma `charFun_map_sum_pi_eq_prod` / 引理 `charFun_map_sum_pi_eq_prod`

English:
lemma charFun_map_sum_pi_eq_prod
  statement: [Fintype ι] [InnerProductSpace Real E]
  proof: by
  ext
  simp [charFun_eq_charFunDual_toDualMap, charFunDual_map_sum_pi_eq_prod]

中文:
引理 charFun_map_sum_pi_eq_prod
  结论: [Fintype ι] [InnerProductSpace 实数 E]
  证明: by
  ext
  simp [charFun_eq_charFunDual_toDualMap, charFunDual_map_sum_pi_eq_prod]

Depends on / 依赖: charFunDual_map_sum_pi_eq_prod, charFun_eq_charFunDual_toDualMap
-/
lemma charFun_map_sum_pi_eq_prod [Fintype ι] [InnerProductSpace Real E]
    (μ : ι -> Measure E) [forall i, IsProbabilityMeasure (μ i)] :
    charFun ((Measure.pi μ).map (fun p => ∑ i, p i)) = ∏ i, charFun (μ i) := by
  ext
  simp [charFun_eq_charFunDual_toDualMap, charFunDual_map_sum_pi_eq_prod]

end Sum

variable [Fintype ι] [IsProbabilityMeasure P] {E : ι -> Type*}
  {mE : forall i, MeasurableSpace (E i)} [forall i, NormedAddCommGroup (E i)] [forall i, CompleteSpace (E i)]
  [forall i, BorelSpace (E i)] [forall i, SecondCountableTopology (E i)] {X : (i : ι) -> Ω -> E i}

section InnerProductSpace

variable [forall i, InnerProductSpace Real (E i)]

/--
lemma `iIndepFun_iff_charFun_pi` / 引理 `iIndepFun_iff_charFun_pi`

English:
lemma iIndepFun_iff_charFun_pi
  given: (hX : forall i, AEMeasurable (X i) P)
  proof: by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX]; rw [← charFun_eq_pi_iff]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]; rw [Function.comp_def]

中文:
引理 iIndepFun_iff_charFun_pi
  条件: (hX : 对任意 i, AEMeasurable (X i) P)
  证明: by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX]; rw [← charFun_eq_pi_iff]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]; rw [Function.comp_def]

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, Function, Function.comp_def, charFun_eq_pi_iff, comp_def, fun_prop, iIndepFun_iff_map_fun_eq_pi_map, map_map_of_aemeasurable
-/
lemma iIndepFun_iff_charFun_pi (hX : forall i, AEMeasurable (X i) P) :
    iIndepFun X P ↔ forall t, charFun (P.map (fun ω => toLp 2 (X · ω))) t =
      ∏ i, charFun (P.map (X i)) (t i) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX]; rw [← charFun_eq_pi_iff]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]; rw [Function.comp_def]

end InnerProductSpace

section NormedSpace

variable [forall i, NormedSpace Real (E i)] [DecidableEq ι]

/--
lemma `iIndepFun_iff_charFunDual_pi` / 引理 `iIndepFun_iff_charFunDual_pi`

English:
lemma iIndepFun_iff_charFunDual_pi
  given: (hX : forall i, AEMeasurable (X i) P)
  proof: by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX]; rw [← charFunDual_eq_pi_iff]

中文:
引理 iIndepFun_iff_charFunDual_pi
  条件: (hX : 对任意 i, AEMeasurable (X i) P)
  证明: by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX]; rw [← charFunDual_eq_pi_iff]

Depends on / 依赖: charFunDual_eq_pi_iff, iIndepFun_iff_map_fun_eq_pi_map
-/
lemma iIndepFun_iff_charFunDual_pi (hX : forall i, AEMeasurable (X i) P) :
    iIndepFun X P ↔ forall L, charFunDual (P.map (fun ω => (X · ω))) L =
      ∏ i, charFunDual (P.map (X i)) (L.comp (.single Real E i)) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX]; rw [← charFunDual_eq_pi_iff]

/--
lemma `iIndepFun_iff_charFunDual_pi'` / 引理 `iIndepFun_iff_charFunDual_pi'`

English:
lemma iIndepFun_iff_charFunDual_pi'
  given: (hX : forall i, AEMeasurable (X i) P)
  proof: by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX]; rw [← charFunDual_eq_pi_iff' p]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]; rw [Function.comp_def]

中文:
引理 iIndepFun_iff_charFunDual_pi'
  条件: (hX : 对任意 i, AEMeasurable (X i) P)
  证明: by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX]; rw [← charFunDual_eq_pi_iff' p]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]; rw [Function.comp_def]

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, Function, Function.comp_def, charFunDual_eq_pi_iff, comp_def, fun_prop, iIndepFun_iff_map_fun_eq_pi_map, map_map_of_aemeasurable
-/
lemma iIndepFun_iff_charFunDual_pi' (hX : forall i, AEMeasurable (X i) P) :
    iIndepFun X P ↔ forall L, charFunDual (P.map (fun ω => toLp p (X · ω))) L =
      ∏ i, charFunDual (P.map (X i)) (L.comp
        ((PiLp.continuousLinearEquiv p Real E).symm.toContinuousLinearMap.comp (.single Real E i))) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX]; rw [← charFunDual_eq_pi_iff' p]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]; rw [Function.comp_def]

end NormedSpace

end iIndepFun

end ProbabilityTheory
