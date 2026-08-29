/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Normed.Operator.NNNorm

/-! # Completeness of spaces of linear and multilinear maps

If `E` is a nontrivial normed space over a nontrivially normed field `𝕜`, and `E` has a
separating dual, then for any normed space `F`, the completeness of the space of continuous
linear maps from `E` to `F` is equivalent to the completeness of `F`.

A similar statement holds for spaces of continuous multilinear maps
-/

public section

open Filter
open scoped Topology

namespace SeparatingDual

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [SeparatingDual 𝕜 E] [Nontrivial E]

/--
lemma `completeSpace_of_completeSpace_continuousLinearMap` / 引理 `completeSpace_of_completeSpace_continuousLinearMap`

English:
lemma completeSpace_of_completeSpace_continuousLinearMap
  given: [CompleteSpace (E ->L[𝕜] F)]
  proof: by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  obtain ⟨v, hv⟩ : exists (v : E), v != 0 := exists_ne 0
  obtain ⟨φ, hφ⟩ : exists φ : StrongDual 𝕜 E, φ v = 1 := exists_eq_one hv
  let g : Nat -> (E ->L[𝕜] F) := fun n => ContinuousLinearMap.smulRightL 𝕜 E F φ (f n)
  have : CauchySeq

中文:
引理 completeSpace_of_completeSpace_continuousLinearMap
  条件: [CompleteSpace (E ->L[𝕜] F)]
  证明: by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  obtain ⟨v, hv⟩ : exists (v : E), v != 0 := exists_ne 0
  obtain ⟨φ, hφ⟩ : exists φ : StrongDual 𝕜 E, φ v = 1 := exists_eq_one hv
  let g : Nat -> (E ->L[𝕜] F) := fun n => ContinuousLinearMap.smulRightL 𝕜 E F φ (f n)
  have : CauchySeq

Depends on / 依赖: CauchySeq, ContinuousLinearMap, ContinuousLinearMap.smulRightL, Metric, Metric.complete_of_cauchySeq_tendsto, StrongDual, Tendsto, cauchySeq_comp, cauchy_iff_exists_le_nhds, cauchy_iff_exists_le_nhds.mp, complete_of_cauchySeq_tendsto, exists_eq_one, exists_ne, lipschitz, lipschitz.cauchySeq_comp, smulRightL
-/
lemma completeSpace_of_completeSpace_continuousLinearMap [CompleteSpace (E ->L[𝕜] F)] :
    CompleteSpace F := by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  obtain ⟨v, hv⟩ : exists (v : E), v != 0 := exists_ne 0
  obtain ⟨φ, hφ⟩ : exists φ : StrongDual 𝕜 E, φ v = 1 := exists_eq_one hv
  let g : Nat -> (E ->L[𝕜] F) := fun n => ContinuousLinearMap.smulRightL 𝕜 E F φ (f n)
  have : CauchySeq g := (ContinuousLinearMap.smulRightL 𝕜 E F φ).lipschitz.cauchySeq_comp hf
  obtain ⟨a, ha⟩ : exists a, Tendsto g atTop (𝓝 a) := cauchy_iff_exists_le_nhds.mp this
  refine ⟨a v, ?_⟩
  have : Tendsto (fun n => g n v) atTop (𝓝 (a v)) := by
    have : Continuous (fun (i : E ->L[𝕜] F) => i v) := by fun_prop
    exact (this.tendsto _).comp ha
  simpa [g, ContinuousLinearMap.smulRightL, hφ]

/--
lemma `completeSpace_continuousLinearMap_iff` / 引理 `completeSpace_continuousLinearMap_iff`

English:
lemma completeSpace_continuousLinearMap_iff
  proof: ⟨fun _h => completeSpace_of_completeSpace_continuousLinearMap 𝕜 E F, fun _h => inferInstance⟩

中文:
引理 completeSpace_continuousLinearMap_iff
  证明: ⟨fun _h => completeSpace_of_completeSpace_continuousLinearMap 𝕜 E F, fun _h => inferInstance⟩

Depends on / 依赖: completeSpace_of_completeSpace_continuousLinearMap
-/
lemma completeSpace_continuousLinearMap_iff :
    CompleteSpace (E ->L[𝕜] F) ↔ CompleteSpace F :=
  ⟨fun _h => completeSpace_of_completeSpace_continuousLinearMap 𝕜 E F, fun _h => inferInstance⟩

open ContinuousMultilinearMap

variable {ι : Type*} [Finite ι] {M : ι -> Type*} [forall i, NormedAddCommGroup (M i)]
  [forall i, NormedSpace 𝕜 (M i)] [forall i, SeparatingDual 𝕜 (M i)]

/--
lemma `completeSpace_of_completeSpace_continuousMultilinearMap` / 引理 `completeSpace_of_completeSpace_continuousMultilinearMap`

English:
lemma completeSpace_of_completeSpace_continuousMultilinearMap
  proof: by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  have : forall i, exists φ : StrongDual 𝕜 (M i), φ (m i) = 1 := fun i => exists_eq_one (hm i)
  choose φ hφ using this
  cases nonempty_fintype ι
  let g : Nat -> (ContinuousMultilinearMap 𝕜 M F) := fun n =>
    compContinuousLinearMap

中文:
引理 completeSpace_of_completeSpace_continuousMultilinearMap
  证明: by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  have : forall i, exists φ : StrongDual 𝕜 (M i), φ (m i) = 1 := fun i => exists_eq_one (hm i)
  choose φ hφ using this
  cases nonempty_fintype ι
  let g : Nat -> (ContinuousMultilinearMap 𝕜 M F) := fun n =>
    compContinuousLinearMap

Depends on / 依赖: CauchySeq, ContinuousLinearMap, ContinuousLinearMap.li, ContinuousLinearMap.lipschitz, ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiAlgebra, ContinuousMultilinearMap.smulRightL, Metric, Metric.complete_of_cauchySeq_tendsto, StrongDual, cauchySeq_comp, compContinuousLinearMapL, complete_of_cauchySeq_tendsto, exists_eq_one, lipschitz, mkPiAlgebra, nonempty_fintype, smulRightL
-/
lemma completeSpace_of_completeSpace_continuousMultilinearMap
    [CompleteSpace (ContinuousMultilinearMap 𝕜 M F)]
    {m : forall i, M i} (hm : forall i, m i != 0) : CompleteSpace F := by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  have : forall i, exists φ : StrongDual 𝕜 (M i), φ (m i) = 1 := fun i => exists_eq_one (hm i)
  choose φ hφ using this
  cases nonempty_fintype ι
  let g : Nat -> (ContinuousMultilinearMap 𝕜 M F) := fun n =>
    compContinuousLinearMapL φ
    (ContinuousMultilinearMap.smulRightL 𝕜 _ F ((ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι 𝕜)) (f n))
  have : CauchySeq g := by
    refine (ContinuousLinearMap.lipschitz _).cauchySeq_comp ?_
    exact (ContinuousLinearMap.lipschitz _).cauchySeq_comp hf
  obtain ⟨a, ha⟩ : exists a, Tendsto g atTop (𝓝 a) := cauchy_iff_exists_le_nhds.mp this
  refine ⟨a m, ?_⟩
  have : Tendsto (fun n => g n m) atTop (𝓝 (a m)) := ((continuous_eval_const _).tendsto _).comp ha
  simpa [g, hφ]

/--
lemma `completeSpace_continuousMultilinearMap_iff` / 引理 `completeSpace_continuousMultilinearMap_iff`

English:
lemma completeSpace_continuousMultilinearMap_iff
  given: {m : forall i, M i} (hm : forall i, m i != 0)
  proof: ⟨fun _h => completeSpace_of_completeSpace_continuousMultilinearMap 𝕜 F hm, fun _h => inferInstance⟩

中文:
引理 completeSpace_continuousMultilinearMap_iff
  条件: {m : 对任意 i, M i} (hm : 对任意 i, m i != 0)
  证明: ⟨fun _h => completeSpace_of_completeSpace_continuousMultilinearMap 𝕜 F hm, fun _h => inferInstance⟩

Depends on / 依赖: completeSpace_of_completeSpace_continuousMultilinearMap
-/
lemma completeSpace_continuousMultilinearMap_iff {m : forall i, M i} (hm : forall i, m i != 0) :
    CompleteSpace (ContinuousMultilinearMap 𝕜 M F) ↔ CompleteSpace F :=
  ⟨fun _h => completeSpace_of_completeSpace_continuousMultilinearMap 𝕜 F hm, fun _h => inferInstance⟩

end SeparatingDual
