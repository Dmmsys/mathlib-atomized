/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Operator.CompleteCodomain
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.ContinuousMap.ContinuousMapZero

/-!
# Continuous linear maps composed with integration

The goal of this file is to prove that integration commutes with continuous linear maps.
This holds for simple functions. The general result follows from the continuity of all involved
operations on the space `L¹`. Note that composition by a continuous linear map on `L¹` is not just
the composition, as we are dealing with classes of functions, but it has already been defined
as `ContinuousLinearMap.compLp`. We take advantage of this construction here.
-/

public section

open MeasureTheory RCLike
open scoped ENNReal NNReal

variable {X Y E F Fₗ : Type*} [MeasurableSpace X] {μ : Measure X} {𝕜 𝕜' : Type*} [RCLike 𝕜]
  [RCLike 𝕜'] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜' F]
  [NormedAddCommGroup Fₗ] [NormedSpace 𝕜 Fₗ] {p : Real>=0∞}

namespace ContinuousLinearMap

variable [NormedSpace Real F] [NormedSpace Real Fₗ]

variable {σ : 𝕜 ->+* 𝕜'} [RingHomIsometric σ]

/--
theorem `integral_compLp` / 定理 `integral_compLp`

English:
theorem integral_compLp
  given: (L : E ->SL[σ] F) (φ : Lp E p μ)
  proof: integral_congr_ae coeFn_compLp _ _

中文:
定理 integral_compLp
  条件: (L : E ->SL[σ] F) (φ : Lp E p μ)
  证明: integral_congr_ae coeFn_compLp _ _

Depends on / 依赖: coeFn_compLp, integral_congr_ae
-/
theorem integral_compLp (L : E ->SL[σ] F) (φ : Lp E p μ) :
    ∫ x, (L.compLp φ) x ∂μ = ∫ x, L (φ x) ∂μ :=
integral_congr_ae coeFn_compLp _ _

/--
theorem `setIntegral_compLp` / 定理 `setIntegral_compLp`

English:
theorem setIntegral_compLp
  given: (L : E ->SL[σ] F) (φ : Lp E p μ) {s : Set X} (hs : MeasurableSet s)
  proof: setIntegral_congr_ae hs ((L.coeFn_compLp φ).mono fun _x hx _ => hx)

中文:
定理 setIntegral_compLp
  条件: (L : E ->SL[σ] F) (φ : Lp E p μ) {s : Set X} (hs : MeasurableSet s)
  证明: setIntegral_congr_ae hs ((L.coeFn_compLp φ).mono fun _x hx _ => hx)

Depends on / 依赖: L.coeFn_compLp, coeFn_compLp, setIntegral_congr_ae
-/
theorem setIntegral_compLp (L : E ->SL[σ] F) (φ : Lp E p μ) {s : Set X} (hs : MeasurableSet s) :
    ∫ x in s, (L.compLp φ) x ∂μ = ∫ x in s, L (φ x) ∂μ :=
  setIntegral_congr_ae hs ((L.coeFn_compLp φ).mono fun _x hx _ => hx)

/--
theorem `continuous_integral_comp_L1` / 定理 `continuous_integral_comp_L1`

English:
theorem continuous_integral_comp_L1
  given: (L : E ->SL[σ] F)
  proof: by
  rw [← funext L.integral_compLp]; exact continuous_integral.comp (L.compLpL 1 μ).continuous

中文:
定理 continuous_integral_comp_L1
  条件: (L : E ->SL[σ] F)
  证明: by
  rw [← funext L.integral_compLp]; exact continuous_integral.comp (L.compLpL 1 μ).continuous

Depends on / 依赖: L.compLpL, L.integral_compLp, compLpL, continuous, continuous_integral, continuous_integral.comp, integral_compLp
-/
theorem continuous_integral_comp_L1 (L : E ->SL[σ] F) :
    Continuous fun φ : X ->₁[μ] E => ∫ x : X, L (φ x) ∂μ := by
  rw [← funext L.integral_compLp]; exact continuous_integral.comp (L.compLpL 1 μ).continuous

variable [CompleteSpace F] [CompleteSpace Fₗ] [NormedSpace Real E]

/--
theorem `integral_comp_commSL` / 定理 `integral_comp_commSL`

English:
theorem integral_comp_commSL
  statement: [CompleteSpace E] (hσ : forall (r : Real) (x : 𝕜), σ (r • x) = r • σ x)
  proof: by
  apply φ_int.induction (P := fun φ => ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ))
  · intro e s s_meas _
    rw [integral_indicator_const e s_meas]; rw [← @smul_one_smul E Real 𝕜 _ _ _ _ _ (μ.real s) e]; rw [map_smulₛₗ]; rw [hσ]; rw [map_one]; rw [smul_assoc]; rw [one_smul]; rw [← integral_indicator_cons

中文:
定理 integral_comp_commSL
  结论: [CompleteSpace E] (hσ : 对任意 (r : 实数) (x : 𝕜), σ (r • x) = r • σ x)
  证明: by
  apply φ_int.induction (P := fun φ => ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ))
  · intro e s s_meas _
    rw [integral_indicator_const e s_meas]; rw [← @smul_one_smul E Real 𝕜 _ _ _ _ _ (μ.real s) e]; rw [map_smulₛₗ]; rw [hσ]; rw [map_one]; rw [smul_assoc]; rw [one_smul]; rw [← integral_indicator_cons

Depends on / 依赖: Function, Function.comp_apply, Function.comp_def, Int.le.intro, Int.ofNat_le, L.map_add, L.map_zero, Nat.le_add_left, Set.indicator_comp_of_zero, _int.induction, add_comm, comp_apply, comp_def, f_int, g_int, indicator_comp_of_zero, integral_add, integral_indicator_const, le_add_left, le_of_neg_le_neg
-/
theorem integral_comp_commSL [CompleteSpace E] (hσ : forall (r : Real) (x : 𝕜), σ (r • x) = r • σ x)
    (L : E ->SL[σ] F) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := by
  apply φ_int.induction (P := fun φ => ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ))
  · intro e s s_meas _
    rw [integral_indicator_const e s_meas]; rw [← @smul_one_smul E Real 𝕜 _ _ _ _ _ (μ.real s) e]; rw [map_smulₛₗ]; rw [hσ]; rw [map_one]; rw [smul_assoc]; rw [one_smul]; rw [← integral_indicator_const (L e) s_meas]
    congr 1 with a
    rw [← Function.comp_def L]; rw [Set.indicator_comp_of_zero L.map_zero]; rw [Function.comp_apply]
  · intro f g _ f_int g_int hf hg
    simp [L.map_add, integral_add (μ := μ) f_int g_int,
      integral_add (μ := μ) (L.integrable_comp f_int) (L.integrable_comp g_int), hf, hg]
  · exact isClosed_eq L.continuous_integral_comp_L1 (L.continuous.comp continuous_integral)
  · intro f g hfg _ hf
    convert! hf using 1 <;> clear hf
    · exact integral_congr_ae (hfg.fun_comp L).symm
    · rw [integral_congr_ae hfg.symm]

/--
theorem `integral_comp_comm` / 定理 `integral_comp_comm`

English:
theorem integral_comp_comm
  given: [CompleteSpace E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ)
  proof: integral_comp_commSL (by simp) L φ_int

中文:
定理 integral_comp_comm
  条件: [CompleteSpace E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : 整数egrable φ μ)
  证明: integral_comp_commSL (by simp) L φ_int

Depends on / 依赖: integral_comp_commSL
-/
theorem integral_comp_comm [CompleteSpace E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := integral_comp_commSL (by simp) L φ_int

/--
theorem `integral_apply` / 定理 `integral_apply`

English:
theorem integral_apply
  statement: {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {φ : X -> H ->L[𝕜] E}
  proof: by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousLinearMap.apply 𝕜 E v).integral_comp_comm φ_int).symm
  · rcases subsingleton_or_nontrivial H with hH | hH
    · simp [Subsingleton.eq_zero v]
    · have : ¬(CompleteSpace (H ->L[𝕜] E)) := by
        rwa [SeparatingDual.completeSpace_continuou

中文:
定理 integral_apply
  结论: {H : 类型} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {φ : X -> H ->L[𝕜] E}
  证明: by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousLinearMap.apply 𝕜 E v).integral_comp_comm φ_int).symm
  · rcases subsingleton_or_nontrivial H with hH | hH
    · simp [Subsingleton.eq_zero v]
    · have : ¬(CompleteSpace (H ->L[𝕜] E)) := by
        rwa [SeparatingDual.completeSpace_continuou

Depends on / 依赖: CompleteSpace, ContinuousLinearMap, ContinuousLinearMap.apply, SeparatingDual, SeparatingDual.completeSpace_continuousLinearMap_iff, Subsingleton, Subsingleton.eq_zero, completeSpace_continuousLinearMap_iff, eq_zero, integral, integral_comp_comm, subsingleton_or_nontrivial
-/
theorem integral_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {φ : X -> H ->L[𝕜] E}
    (φ_int : Integrable φ μ) (v : H) : (∫ x, φ x ∂μ) v = ∫ x, φ x v ∂μ := by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousLinearMap.apply 𝕜 E v).integral_comp_comm φ_int).symm
  · rcases subsingleton_or_nontrivial H with hH | hH
    · simp [Subsingleton.eq_zero v]
    · have : ¬(CompleteSpace (H ->L[𝕜] E)) := by
        rwa [SeparatingDual.completeSpace_continuousLinearMap_iff]
      simp [integral, hE, this]

/--
theorem `_root_.ContinuousMultilinearMap.integral_apply` / 定理 `_root_.ContinuousMultilinearMap.integral_apply`

English:
theorem _root_.ContinuousMultilinearMap.integral_apply
  statement: {ι : Type*} [Fintype ι] {M : ι -> Type*}
  proof: by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousMultilinearMap.apply 𝕜 M E m).integral_comp_comm φ_int).symm
  · by_cases! hm : forall i, m i != 0
    · have : ¬ CompleteSpace (ContinuousMultilinearMap 𝕜 M E) := by
        rwa [SeparatingDual.completeSpace_continuousMultilinearMap_iff _ _ h

中文:
定理 _root_.ContinuousMultilinearMap.integral_apply
  结论: {ι : 类型} [Fintype ι] {M : ι -> 类型}
  证明: by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousMultilinearMap.apply 𝕜 M E m).integral_comp_comm φ_int).symm
  · by_cases! hm : forall i, m i != 0
    · have : ¬ CompleteSpace (ContinuousMultilinearMap 𝕜 M E) := by
        rwa [SeparatingDual.completeSpace_continuousMultilinearMap_iff _ _ h

Depends on / 依赖: CompleteSpace, ContinuousMultilinearMap, ContinuousMultilinearMap.apply, ContinuousMultilinearMap.map_coord_zero, SeparatingDual, SeparatingDual.completeSpace_continuousMultilinearMap_iff, completeSpace_continuousMultilinearMap_iff, integral, integral_comp_comm, map_coord_zero
-/
theorem _root_.ContinuousMultilinearMap.integral_apply {ι : Type*} [Fintype ι] {M : ι -> Type*}
    [forall i, NormedAddCommGroup (M i)] [forall i, NormedSpace 𝕜 (M i)]
    {φ : X -> ContinuousMultilinearMap 𝕜 M E} (φ_int : Integrable φ μ) (m : forall i, M i) :
    (∫ x, φ x ∂μ) m = ∫ x, φ x m ∂μ := by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousMultilinearMap.apply 𝕜 M E m).integral_comp_comm φ_int).symm
  · by_cases! hm : forall i, m i != 0
    · have : ¬ CompleteSpace (ContinuousMultilinearMap 𝕜 M E) := by
        rwa [SeparatingDual.completeSpace_continuousMultilinearMap_iff _ _ hm]
      simp [integral, hE, this]
    · rcases hm with ⟨i, hi⟩
      simp [ContinuousMultilinearMap.map_coord_zero _ i hi]

variable [CompleteSpace E]

/--
theorem `integral_comp_comm'` / 定理 `integral_comp_comm'`

English:
theorem integral_comp_comm'
  given: (L : E ->L[𝕜] Fₗ) {K} (hL : AntilipschitzWith K L) (φ : X -> E)
  proof: by
  by_cases h : Integrable φ μ
  · exact integral_comp_comm L h
  have : ¬Integrable (fun x => L (φ x)) μ := by
    rwa [← Function.comp_def,
      LipschitzWith.integrable_comp_iff_of_antilipschitz L.lipschitz hL L.map_zero]
  simp [integral_undef, h, this]

中文:
定理 integral_comp_comm'
  条件: (L : E ->L[𝕜] Fₗ) {K} (hL : AntilipschitzWith K L) (φ : X -> E)
  证明: by
  by_cases h : Integrable φ μ
  · exact integral_comp_comm L h
  have : ¬Integrable (fun x => L (φ x)) μ := by
    rwa [← Function.comp_def,
      LipschitzWith.integrable_comp_iff_of_antilipschitz L.lipschitz hL L.map_zero]
  simp [integral_undef, h, this]

Depends on / 依赖: Function, Function.comp_def, Integrable, L.lipschitz, L.map_zero, LipschitzWith, LipschitzWith.integrable_comp_iff_of_antilipschitz, comp_def, integrable_comp_iff_of_antilipschitz, integral_comp_comm, integral_undef, lipschitz, map_zero
-/
theorem integral_comp_comm' (L : E ->L[𝕜] Fₗ) {K} (hL : AntilipschitzWith K L) (φ : X -> E) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := by
  by_cases h : Integrable φ μ
  · exact integral_comp_comm L h
  have : ¬Integrable (fun x => L (φ x)) μ := by
    rwa [← Function.comp_def,
      LipschitzWith.integrable_comp_iff_of_antilipschitz L.lipschitz hL L.map_zero]
  simp [integral_undef, h, this]

/--
theorem `integral_comp_L1_comm` / 定理 `integral_comp_L1_comm`

English:
theorem integral_comp_L1_comm
  given: (L : E ->L[𝕜] Fₗ) (φ : X ->₁[μ] E)
  proof: L.integral_comp_comm (L1.integrable_coeFn φ)

中文:
定理 integral_comp_L1_comm
  条件: (L : E ->L[𝕜] Fₗ) (φ : X ->₁[μ] E)
  证明: L.integral_comp_comm (L1.integrable_coeFn φ)

Depends on / 依赖: L.integral_comp_comm, L1.integrable_coeFn, integrable_coeFn, integral_comp_comm
-/
theorem integral_comp_L1_comm (L : E ->L[𝕜] Fₗ) (φ : X ->₁[μ] E) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) :=
  L.integral_comp_comm (L1.integrable_coeFn φ)

end ContinuousLinearMap

namespace LinearIsometry

variable [CompleteSpace F] [NormedSpace 𝕜 F] [NormedSpace Real F] [CompleteSpace E] [NormedSpace Real E]

/--
theorem `integral_comp_comm` / 定理 `integral_comp_comm`

English:
theorem integral_comp_comm
  given: (L : E ->ₗᵢ[𝕜] F) (φ : X -> E)
  statement: ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
  proof: L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _

中文:
定理 integral_comp_comm
  条件: (L : E ->ₗᵢ[𝕜] F) (φ : X -> E)
  结论: ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
  证明: L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _

Depends on / 依赖: L.antilipschitz, L.toContinuousLinearMap.integral_comp_comm, antilipschitz, integral_comp_comm, toContinuousLinearMap
-/
theorem integral_comp_comm (L : E ->ₗᵢ[𝕜] F) (φ : X -> E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) :=
  L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _

end LinearIsometry

namespace ContinuousLinearEquiv

variable [NormedSpace Real F] [NormedSpace 𝕜 F] [NormedSpace Real E]

/--
theorem `integral_comp_comm` / 定理 `integral_comp_comm`

English:
theorem integral_comp_comm
  given: (L : E ≃L[𝕜] F) (φ : X -> E)
  statement: ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
  proof: by
  have : CompleteSpace E ↔ CompleteSpace F :=
    completeSpace_congr (e := L.toEquiv) L.isUniformEmbedding
  obtain ⟨_, _⟩ | ⟨_, _⟩ := iff_iff_and_or_not_and_not.mp this
  · exact L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _
  · simp [integral, *]

中文:
定理 integral_comp_comm
  条件: (L : E ≃L[𝕜] F) (φ : X -> E)
  结论: ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
  证明: by
  have : CompleteSpace E ↔ CompleteSpace F :=
    completeSpace_congr (e := L.toEquiv) L.isUniformEmbedding
  obtain ⟨_, _⟩ | ⟨_, _⟩ := iff_iff_and_or_not_and_not.mp this
  · exact L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _
  · simp [integral, *]

Depends on / 依赖: CompleteSpace, L.antilipschitz, L.isUniformEmbedding, L.toContinuousLinearMap.integral_comp_comm, L.toEquiv, antilipschitz, completeSpace_congr, iff_iff_and_or_not_and_not, iff_iff_and_or_not_and_not.mp, integral, integral_comp_comm, isUniformEmbedding, toContinuousLinearMap, toEquiv
-/
theorem integral_comp_comm (L : E ≃L[𝕜] F) (φ : X -> E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := by
  have : CompleteSpace E ↔ CompleteSpace F :=
    completeSpace_congr (e := L.toEquiv) L.isUniformEmbedding
  obtain ⟨_, _⟩ | ⟨_, _⟩ := iff_iff_and_or_not_and_not.mp this
  · exact L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _
  · simp [integral, *]

end ContinuousLinearEquiv

section ContinuousMap

variable [TopologicalSpace Y] [CompactSpace Y]

/--
lemma `ContinuousMap.integral_apply` / 引理 `ContinuousMap.integral_apply`

English:
lemma ContinuousMap.integral_apply
  statement: [NormedSpace Real E] [CompleteSpace E] {f : X -> C(Y, E)}
  proof: by
  calc (∫ x, f x ∂μ) y = ContinuousMap.evalCLM Real y (∫ x, f x ∂μ) := rfl
    _ = ∫ x, ContinuousMap.evalCLM Real y (f x) ∂μ :=
          (ContinuousLinearMap.integral_comp_comm _ hf).symm
    _ = _ := rfl

中文:
引理 ContinuousMap.integral_apply
  结论: [NormedSpace 实数 E] [CompleteSpace E] {f : X -> C(Y, E)}
  证明: by
  calc (∫ x, f x ∂μ) y = ContinuousMap.evalCLM Real y (∫ x, f x ∂μ) := rfl
    _ = ∫ x, ContinuousMap.evalCLM Real y (f x) ∂μ :=
          (ContinuousLinearMap.integral_comp_comm _ hf).symm
    _ = _ := rfl

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integral_comp_comm, ContinuousMap, ContinuousMap.evalCLM, evalCLM, integral_comp_comm
-/
lemma ContinuousMap.integral_apply [NormedSpace Real E] [CompleteSpace E] {f : X -> C(Y, E)}
    (hf : Integrable f μ) (y : Y) : (∫ x, f x ∂μ) y = ∫ x, f x y ∂μ := by
  calc (∫ x, f x ∂μ) y = ContinuousMap.evalCLM Real y (∫ x, f x ∂μ) := rfl
    _ = ∫ x, ContinuousMap.evalCLM Real y (f x) ∂μ :=
          (ContinuousLinearMap.integral_comp_comm _ hf).symm
    _ = _ := rfl

open scoped ContinuousMapZero in
/--
theorem `ContinuousMapZero.integral_apply` / 定理 `ContinuousMapZero.integral_apply`

English:
theorem ContinuousMapZero.integral_apply
  statement: {R : Type*} [NormedCommRing R] [Zero Y]
  proof: by
  calc (∫ x, f x ∂μ) y = ContinuousMapZero.evalCLM Real y (∫ x, f x ∂μ) := rfl
    _ = ∫ x, ContinuousMapZero.evalCLM Real y (f x) ∂μ :=
          (ContinuousLinearMap.integral_comp_comm _ hf).symm
    _ = _ := rfl

中文:
定理 ContinuousMapZero.integral_apply
  结论: {R : 类型} [NormedCommRing R] [Zero Y]
  证明: by
  calc (∫ x, f x ∂μ) y = ContinuousMapZero.evalCLM Real y (∫ x, f x ∂μ) := rfl
    _ = ∫ x, ContinuousMapZero.evalCLM Real y (f x) ∂μ :=
          (ContinuousLinearMap.integral_comp_comm _ hf).symm
    _ = _ := rfl

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integral_comp_comm, ContinuousMapZero, ContinuousMapZero.evalCLM, evalCLM, integral_comp_comm
-/
theorem ContinuousMapZero.integral_apply {R : Type*} [NormedCommRing R] [Zero Y]
    [NormedAlgebra Real R] [CompleteSpace R] {f : X -> C(Y, R)₀}
    (hf : MeasureTheory.Integrable f μ) (y : Y) :
    (∫ (x : X), f x ∂μ) y = ∫ (x : X), (f x) y ∂μ := by
  calc (∫ x, f x ∂μ) y = ContinuousMapZero.evalCLM Real y (∫ x, f x ∂μ) := rfl
    _ = ∫ x, ContinuousMapZero.evalCLM Real y (f x) ∂μ :=
          (ContinuousLinearMap.integral_comp_comm _ hf).symm
    _ = _ := rfl

end ContinuousMap

@[norm_cast]
/--
theorem `integral_ofReal` / 定理 `integral_ofReal`

English:
theorem integral_ofReal
  given: {f : X -> Real}
  statement: ∫ x, (f x : 𝕜) ∂μ = ↑(∫ x, f x ∂μ)
  proof: (@RCLike.ofRealLI 𝕜 _).integral_comp_comm f

@[norm_cast]

中文:
定理 integral_ofReal
  条件: {f : X -> 实数}
  结论: ∫ x, (f x : 𝕜) ∂μ = ↑(∫ x, f x ∂μ)
  证明: (@RCLike.ofRealLI 𝕜 _).integral_comp_comm f

@[norm_cast]

Depends on / 依赖: RCLike, RCLike.ofRealLI, integral_comp_comm, ofRealLI
-/
theorem integral_ofReal {f : X -> Real} : ∫ x, (f x : 𝕜) ∂μ = ↑(∫ x, f x ∂μ) :=
  (@RCLike.ofRealLI 𝕜 _).integral_comp_comm f

@[norm_cast]
/--
theorem `integral_complex_ofReal` / 定理 `integral_complex_ofReal`

English:
theorem integral_complex_ofReal
  given: {f : X -> Real}
  statement: ∫ x, (f x : Complex) ∂μ = ∫ x, f x ∂μ
  proof: integral_ofReal

中文:
定理 integral_complex_ofReal
  条件: {f : X -> 实数}
  结论: ∫ x, (f x : Complex) ∂μ = ∫ x, f x ∂μ
  证明: integral_ofReal

Depends on / 依赖: integral_ofReal
-/
theorem integral_complex_ofReal {f : X -> Real} : ∫ x, (f x : Complex) ∂μ = ∫ x, f x ∂μ := integral_ofReal

/--
theorem `integral_re` / 定理 `integral_re`

English:
theorem integral_re
  given: {f : X -> 𝕜} (hf : Integrable f μ)
  proof: (@RCLike.reCLM 𝕜 _).integral_comp_comm hf

中文:
定理 integral_re
  条件: {f : X -> 𝕜} (hf : 整数egrable f μ)
  证明: (@RCLike.reCLM 𝕜 _).integral_comp_comm hf

Depends on / 依赖: RCLike, RCLike.reCLM, integral_comp_comm
-/
theorem integral_re {f : X -> 𝕜} (hf : Integrable f μ) :
    ∫ x, RCLike.re (f x) ∂μ = RCLike.re (∫ x, f x ∂μ) :=
  (@RCLike.reCLM 𝕜 _).integral_comp_comm hf

/--
theorem `integral_im` / 定理 `integral_im`

English:
theorem integral_im
  given: {f : X -> 𝕜} (hf : Integrable f μ)
  proof: (@RCLike.imCLM 𝕜 _).integral_comp_comm hf

中文:
定理 integral_im
  条件: {f : X -> 𝕜} (hf : 整数egrable f μ)
  证明: (@RCLike.imCLM 𝕜 _).integral_comp_comm hf

Depends on / 依赖: RCLike, RCLike.imCLM, integral_comp_comm
-/
theorem integral_im {f : X -> 𝕜} (hf : Integrable f μ) :
    ∫ x, RCLike.im (f x) ∂μ = RCLike.im (∫ x, f x ∂μ) :=
  (@RCLike.imCLM 𝕜 _).integral_comp_comm hf

open scoped ComplexConjugate in
/--
theorem `integral_conj` / 定理 `integral_conj`

English:
theorem integral_conj
  given: {f : X -> 𝕜}
  statement: ∫ x, conj (f x) ∂μ = conj (∫ x, f x ∂μ)
  proof: (@RCLike.conjLIE 𝕜 _).toLinearIsometry.integral_comp_comm f

中文:
定理 integral_conj
  条件: {f : X -> 𝕜}
  结论: ∫ x, conj (f x) ∂μ = conj (∫ x, f x ∂μ)
  证明: (@RCLike.conjLIE 𝕜 _).toLinearIsometry.integral_comp_comm f

Depends on / 依赖: RCLike, RCLike.conjLIE, conjLIE, integral_comp_comm, toLinearIsometry, toLinearIsometry.integral_comp_comm
-/
theorem integral_conj {f : X -> 𝕜} : ∫ x, conj (f x) ∂μ = conj (∫ x, f x ∂μ) :=
  (@RCLike.conjLIE 𝕜 _).toLinearIsometry.integral_comp_comm f

/--
theorem `integral_coe_re_add_coe_im` / 定理 `integral_coe_re_add_coe_im`

English:
theorem integral_coe_re_add_coe_im
  given: {f : X -> 𝕜} (hf : Integrable f μ)
  proof: by
  rw [mul_comm]; rw [← smul_eq_mul]; rw [← integral_smul]; rw [← integral_add]
  · congr
    ext1 x
    rw [smul_eq_mul]; rw [mul_comm]; rw [RCLike.re_add_im]
  · exact hf.re.ofReal
  · exact hf.im.ofReal.smul (𝕜 := 𝕜) (β := 𝕜) RCLike.I

中文:
定理 integral_coe_re_add_coe_im
  条件: {f : X -> 𝕜} (hf : 整数egrable f μ)
  证明: by
  rw [mul_comm]; rw [← smul_eq_mul]; rw [← integral_smul]; rw [← integral_add]
  · congr
    ext1 x
    rw [smul_eq_mul]; rw [mul_comm]; rw [RCLike.re_add_im]
  · exact hf.re.ofReal
  · exact hf.im.ofReal.smul (𝕜 := 𝕜) (β := 𝕜) RCLike.I

Depends on / 依赖: RCLike, RCLike.I, RCLike.re_add_im, hf.im.ofReal.smul, hf.re.ofReal, integral_add, integral_smul, mul_comm, ofReal, re_add_im, smul_eq_mul
-/
theorem integral_coe_re_add_coe_im {f : X -> 𝕜} (hf : Integrable f μ) :
    ∫ x, (re (f x) : 𝕜) ∂μ + (∫ x, (im (f x) : 𝕜) ∂μ) * RCLike.I = ∫ x, f x ∂μ := by
  rw [mul_comm]; rw [← smul_eq_mul]; rw [← integral_smul]; rw [← integral_add]
  · congr
    ext1 x
    rw [smul_eq_mul]; rw [mul_comm]; rw [RCLike.re_add_im]
  · exact hf.re.ofReal
  · exact hf.im.ofReal.smul (𝕜 := 𝕜) (β := 𝕜) RCLike.I

/--
theorem `integral_re_add_im` / 定理 `integral_re_add_im`

English:
theorem integral_re_add_im
  given: {f : X -> 𝕜} (hf : Integrable f μ)
  proof: by
  rw [← integral_ofReal]; rw [← integral_ofReal]; rw [integral_coe_re_add_coe_im hf]

中文:
定理 integral_re_add_im
  条件: {f : X -> 𝕜} (hf : 整数egrable f μ)
  证明: by
  rw [← integral_ofReal]; rw [← integral_ofReal]; rw [integral_coe_re_add_coe_im hf]

Depends on / 依赖: integral_coe_re_add_coe_im, integral_ofReal
-/
theorem integral_re_add_im {f : X -> 𝕜} (hf : Integrable f μ) :
    ((∫ x, RCLike.re (f x) ∂μ : Real) : 𝕜) + (∫ x, RCLike.im (f x) ∂μ : Real) * RCLike.I =
      ∫ x, f x ∂μ := by
  rw [← integral_ofReal]; rw [← integral_ofReal]; rw [integral_coe_re_add_coe_im hf]

/--
theorem `setIntegral_re_add_im` / 定理 `setIntegral_re_add_im`

English:
theorem setIntegral_re_add_im
  given: {f : X -> 𝕜} {i : Set X} (hf : IntegrableOn f i μ)
  proof: integral_re_add_im hf

中文:
定理 setIntegral_re_add_im
  条件: {f : X -> 𝕜} {i : Set X} (hf : 整数egrableOn f i μ)
  证明: integral_re_add_im hf

Depends on / 依赖: integral_re_add_im
-/
theorem setIntegral_re_add_im {f : X -> 𝕜} {i : Set X} (hf : IntegrableOn f i μ) :
    ((∫ x in i, RCLike.re (f x) ∂μ : Real) : 𝕜) + (∫ x in i, RCLike.im (f x) ∂μ : Real) * RCLike.I =
      ∫ x in i, f x ∂μ :=
  integral_re_add_im hf

variable [NormedSpace Real E] [NormedSpace Real F]

/--
lemma `swap_integral` / 引理 `swap_integral`

English:
lemma swap_integral
  given: (f : X -> E × F)
  statement: (∫ x, f x ∂μ).swap = ∫ x, (f x).swap ∂μ
  proof: .symm (ContinuousLinearEquiv.prodComm Real E F).integral_comp_comm f

中文:
引理 swap_integral
  条件: (f : X -> E × F)
  结论: (∫ x, f x ∂μ).swap = ∫ x, (f x).swap ∂μ
  证明: .symm (ContinuousLinearEquiv.prodComm Real E F).integral_comp_comm f

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.prodComm, integral_comp_comm, prodComm
-/
lemma swap_integral (f : X -> E × F) : (∫ x, f x ∂μ).swap = ∫ x, (f x).swap ∂μ :=
.symm (ContinuousLinearEquiv.prodComm Real E F).integral_comp_comm f

/--
theorem `fst_integral` / 定理 `fst_integral`

English:
theorem fst_integral
  given: [CompleteSpace F] {f : X -> E × F} (hf : Integrable f μ)
  proof: by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousLinearMap.fst Real E F).integral_comp_comm hf).symm
· have : ¬(CompleteSpace (E × F)) := fun h => hE .fst_of_prod (β := F)
    simp [integral, *]

中文:
定理 fst_integral
  条件: [CompleteSpace F] {f : X -> E × F} (hf : 整数egrable f μ)
  证明: by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousLinearMap.fst Real E F).integral_comp_comm hf).symm
· have : ¬(CompleteSpace (E × F)) := fun h => hE .fst_of_prod (β := F)
    simp [integral, *]

Depends on / 依赖: CompleteSpace, ContinuousLinearMap, ContinuousLinearMap.fst, fst_of_prod, integral, integral_comp_comm
-/
theorem fst_integral [CompleteSpace F] {f : X -> E × F} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ := by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousLinearMap.fst Real E F).integral_comp_comm hf).symm
· have : ¬(CompleteSpace (E × F)) := fun h => hE .fst_of_prod (β := F)
    simp [integral, *]

/--
theorem `snd_integral` / 定理 `snd_integral`

English:
theorem snd_integral
  given: [CompleteSpace E] {f : X -> E × F} (hf : Integrable f μ)
  proof: by
  rw [← Prod.fst_swap]; rw [swap_integral]
exact fst_integral hf.snd.prodMk hf.fst

中文:
定理 snd_integral
  条件: [CompleteSpace E] {f : X -> E × F} (hf : 整数egrable f μ)
  证明: by
  rw [← Prod.fst_swap]; rw [swap_integral]
exact fst_integral hf.snd.prodMk hf.fst

Depends on / 依赖: Prod.fst_swap, fst_integral, fst_swap, hf.fst, hf.snd.prodMk, prodMk, swap_integral
-/
theorem snd_integral [CompleteSpace E] {f : X -> E × F} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ := by
  rw [← Prod.fst_swap]; rw [swap_integral]
exact fst_integral hf.snd.prodMk hf.fst

/--
theorem `integral_pair` / 定理 `integral_pair`

English:
theorem integral_pair
  statement: [CompleteSpace E] [CompleteSpace F] {f : X -> E} {g : X -> F}
  proof: have := hf.prodMk hg
  Prod.ext (fst_integral this) (snd_integral this)

中文:
定理 integral_pair
  结论: [CompleteSpace E] [CompleteSpace F] {f : X -> E} {g : X -> F}
  证明: have := hf.prodMk hg
  Prod.ext (fst_integral this) (snd_integral this)

Depends on / 依赖: Prod.ext, fst_integral, hf.prodMk, prodMk, snd_integral
-/
theorem integral_pair [CompleteSpace E] [CompleteSpace F] {f : X -> E} {g : X -> F}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, (f x, g x) ∂μ = (∫ x, f x ∂μ, ∫ x, g x ∂μ) :=
  have := hf.prodMk hg
  Prod.ext (fst_integral this) (snd_integral this)

/--
theorem `integral_smul_const` / 定理 `integral_smul_const`

English:
theorem integral_smul_const
  statement: {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E]
  proof: by
  by_cases hf : Integrable f μ
  · exact ((1 : 𝕜 ->L[𝕜] 𝕜).smulRight c).integral_comp_comm hf
  · by_cases hc : c = 0
    · simp [hc, integral_zero, smul_zero]
    rw [integral_undef hf]; rw [integral_undef]; rw [zero_smul]
    rw [integrable_smul_const hc]
    simp_rw [hf, not_false_eq_true]

中文:
定理 integral_smul_const
  结论: {𝕜 : 类型} [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E]
  证明: by
  by_cases hf : Integrable f μ
  · exact ((1 : 𝕜 ->L[𝕜] 𝕜).smulRight c).integral_comp_comm hf
  · by_cases hc : c = 0
    · simp [hc, integral_zero, smul_zero]
    rw [integral_undef hf]; rw [integral_undef]; rw [zero_smul]
    rw [integrable_smul_const hc]
    simp_rw [hf, not_false_eq_true]

Depends on / 依赖: Integrable, integrable_smul_const, integral_comp_comm, integral_undef, integral_zero, not_false_eq_true, simp_rw, smulRight, smul_zero, zero_smul
-/
theorem integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E]
    (f : X -> 𝕜) (c : E) :
    ∫ x, f x • c ∂μ = (∫ x, f x ∂μ) • c := by
  by_cases hf : Integrable f μ
  · exact ((1 : 𝕜 ->L[𝕜] 𝕜).smulRight c).integral_comp_comm hf
  · by_cases hc : c = 0
    · simp [hc, integral_zero, smul_zero]
    rw [integral_undef hf]; rw [integral_undef]; rw [zero_smul]
    rw [integrable_smul_const hc]
    simp_rw [hf, not_false_eq_true]

/--
lemma `integral_const_mul_of_integrable` / 引理 `integral_const_mul_of_integrable`

English:
lemma integral_const_mul_of_integrable
  statement: {A : Type*} [NonUnitalNormedRing A] [NormedSpace Real A]
  proof: by
  by_cases hA : CompleteSpace A
  · change ∫ x, ContinuousLinearMap.mul Real _ c (f x) ∂μ = ContinuousLinearMap.mul Real _ c (∫ x, f x ∂μ)
    rw [ContinuousLinearMap.integral_comp_comm _ hf]
  · simp [integral, hA]

中文:
引理 integral_const_mul_of_integrable
  结论: {A : 类型} [NonUnitalNormedRing A] [NormedSpace 实数 A]
  证明: by
  by_cases hA : CompleteSpace A
  · change ∫ x, ContinuousLinearMap.mul Real _ c (f x) ∂μ = ContinuousLinearMap.mul Real _ c (∫ x, f x ∂μ)
    rw [ContinuousLinearMap.integral_comp_comm _ hf]
  · simp [integral, hA]

Depends on / 依赖: CompleteSpace, ContinuousLinearMap, ContinuousLinearMap.integral_comp_comm, ContinuousLinearMap.mul, integral, integral_comp_comm
-/
lemma integral_const_mul_of_integrable {A : Type*} [NonUnitalNormedRing A] [NormedSpace Real A]
    [IsScalarTower Real A A] [SMulCommClass Real A A] {f : X -> A} (hf : Integrable f μ) {c : A} :
    ∫ x, c * f x ∂μ = c * ∫ x, f x ∂μ := by
  by_cases hA : CompleteSpace A
  · change ∫ x, ContinuousLinearMap.mul Real _ c (f x) ∂μ = ContinuousLinearMap.mul Real _ c (∫ x, f x ∂μ)
    rw [ContinuousLinearMap.integral_comp_comm _ hf]
  · simp [integral, hA]

/--
lemma `integral_mul_const_of_integrable` / 引理 `integral_mul_const_of_integrable`

English:
lemma integral_mul_const_of_integrable
  statement: {A : Type*} [NonUnitalNormedRing A] [NormedSpace Real A]
  proof: by
  by_cases hA : CompleteSpace A
  · change ∫ x, (ContinuousLinearMap.mul Real _).flip c (f x) ∂μ
      = (ContinuousLinearMap.mul Real _).flip c (∫ x, f x ∂μ)
    rw [ContinuousLinearMap.integral_comp_comm _ hf]
  · simp [integral, hA]

中文:
引理 integral_mul_const_of_integrable
  结论: {A : 类型} [NonUnitalNormedRing A] [NormedSpace 实数 A]
  证明: by
  by_cases hA : CompleteSpace A
  · change ∫ x, (ContinuousLinearMap.mul Real _).flip c (f x) ∂μ
      = (ContinuousLinearMap.mul Real _).flip c (∫ x, f x ∂μ)
    rw [ContinuousLinearMap.integral_comp_comm _ hf]
  · simp [integral, hA]

Depends on / 依赖: CompleteSpace, ContinuousLinearMap, ContinuousLinearMap.integral_comp_comm, ContinuousLinearMap.mul, integral, integral_comp_comm
-/
lemma integral_mul_const_of_integrable {A : Type*} [NonUnitalNormedRing A] [NormedSpace Real A]
    [IsScalarTower Real A A] [SMulCommClass Real A A] {f : X -> A} (hf : Integrable f μ) {c : A} :
    ∫ x, f x * c ∂μ = (∫ x, f x ∂μ) * c := by
  by_cases hA : CompleteSpace A
  · change ∫ x, (ContinuousLinearMap.mul Real _).flip c (f x) ∂μ
      = (ContinuousLinearMap.mul Real _).flip c (∫ x, f x ∂μ)
    rw [ContinuousLinearMap.integral_comp_comm _ hf]
  · simp [integral, hA]

/--
theorem `integral_withDensity_eq_integral_smul` / 定理 `integral_withDensity_eq_integral_smul`

English:
theorem integral_withDensity_eq_integral_smul
  given: {f : X -> Real>=0} (f_meas : Measurable f) (g : X -> E)
  proof: by
  by_cases hE : CompleteSpace E; swap; · simp [integral, hE]
  by_cases hg : Integrable g (μ.withDensity fun x => f x); swap
  · rw [integral_undef hg, integral_undef]
    rwa [← integrable_withDensity_iff_integrable_smul f_meas]
  refine Integrable.induction
    (P := fun g => ∫ x, g x ∂μ.withDe

中文:
定理 integral_withDensity_eq_integral_smul
  条件: {f : X -> 实数>=0} (f_meas : Measurable f) (g : X -> E)
  证明: by
  by_cases hE : CompleteSpace E; swap; · simp [integral, hE]
  by_cases hg : Integrable g (μ.withDensity fun x => f x); swap
  · rw [integral_undef hg, integral_undef]
    rwa [← integrable_withDensity_iff_integrable_smul f_meas]
  refine Integrable.induction
    (P := fun g => ∫ x, g x ∂μ.withDe

Depends on / 依赖: CompleteSpace, Integrable, Integrable.induction, Measure, Set.indicator_smul_apply, f_meas, indicator_smul_apply, integrable_withDensity_iff_integrable_smul, integral, integral_const, integral_indicator, integral_undef, s_meas, simp_rw, withDensity
-/
theorem integral_withDensity_eq_integral_smul {f : X -> Real>=0} (f_meas : Measurable f) (g : X -> E) :
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ := by
  by_cases hE : CompleteSpace E; swap; · simp [integral, hE]
  by_cases hg : Integrable g (μ.withDensity fun x => f x); swap
  · rw [integral_undef hg, integral_undef]
    rwa [← integrable_withDensity_iff_integrable_smul f_meas]
  refine Integrable.induction
    (P := fun g => ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ) ?_ ?_ ?_ ?_ hg
  · intro c s s_meas hs
    rw [integral_indicator s_meas]
    simp_rw [← Set.indicator_smul_apply, integral_indicator s_meas]
    simp only [s_meas, integral_const, Measure.restrict_apply', Set.univ_inter, withDensity_apply,
      measureReal_def]
    rw [lintegral_coe_eq_integral]; rw [ENNReal.toReal_ofReal]; rw [← integral_smul_const]
    · rfl
    · exact integral_nonneg fun x => NNReal.coe_nonneg _
    · refine ⟨f_meas.coe_nnreal_real.aemeasurable.aestronglyMeasurable, ?_⟩
      simpa [withDensity_apply _ s_meas, hasFiniteIntegral_iff_enorm] using hs
  · intro u u' _ u_int u'_int h h'
    change
      (∫ x : X, u x + u' x ∂μ.withDensity fun x : X => ↑(f x)) = ∫ x : X, f x • (u x + u' x) ∂μ
    simp_rw [smul_add]
    rw [integral_add u_int u'_int]; rw [h]; rw [h']; rw [integral_add]
    · exact (integrable_withDensity_iff_integrable_smul f_meas).1 u_int
    · exact (integrable_withDensity_iff_integrable_smul f_meas).1 u'_int
  · have C1 :
      Continuous fun u : Lp E 1 (μ.withDensity fun x => f x) =>
        ∫ x, u x ∂μ.withDensity fun x => f x :=
      continuous_integral
    have C2 : Continuous fun u : Lp E 1 (μ.withDensity fun x => f x) => ∫ x, f x • u x ∂μ := by
      have : Continuous ((fun u : Lp E 1 μ => ∫ x, u x ∂μ) ∘ withDensitySMulLI (E := E) μ f_meas) :=
        continuous_integral.comp (withDensitySMulLI (E := E) μ f_meas).continuous
      convert! this with u
      simp only [Function.comp_apply, withDensitySMulLI_apply]
      exact integral_congr_ae (memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp.symm
    exact isClosed_eq C1 C2
  · intro u v huv _ hu
    rw [← integral_congr_ae huv]; rw [hu]
    apply integral_congr_ae
    filter_upwards [(ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 huv] with x hx
    rcases eq_or_ne (f x) 0 with (h'x | h'x)
    · simp only [h'x, zero_smul]
    · rw [hx _]
      simpa only [Ne, ENNReal.coe_eq_zero] using h'x

/--
theorem `integral_withDensity_eq_integral_smul₀` / 定理 `integral_withDensity_eq_integral_smul₀`

English:
theorem integral_withDensity_eq_integral_smul₀
  given: {f : X -> Real>=0} (hf : AEMeasurable f μ) (g : X -> E)
  proof: by
  let f' := hf.mk _
  calc
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, g x ∂μ.withDensity fun x => f' x := by
      congr 1
      apply withDensity_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]
    _ = ∫ x, f' x • g x ∂μ := integral_withDensity_eq_integral_smul hf.meas

中文:
定理 integral_withDensity_eq_integral_smul₀
  条件: {f : X -> 实数>=0} (hf : AEMeasurable f μ) (g : X -> E)
  证明: by
  let f' := hf.mk _
  calc
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, g x ∂μ.withDensity fun x => f' x := by
      congr 1
      apply withDensity_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]
    _ = ∫ x, f' x • g x ∂μ := integral_withDensity_eq_integral_smul hf.meas

Depends on / 依赖: ae_eq_mk, filter_upwards, hf.ae_eq_mk, hf.measurable_mk, hf.mk, integral_congr_ae, integral_withDensity_eq_integral_smul, measurable_mk, withDensity, withDensity_congr_ae
-/
theorem integral_withDensity_eq_integral_smul₀ {f : X -> Real>=0} (hf : AEMeasurable f μ) (g : X -> E) :
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ := by
  let f' := hf.mk _
  calc
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, g x ∂μ.withDensity fun x => f' x := by
      congr 1
      apply withDensity_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]
    _ = ∫ x, f' x • g x ∂μ := integral_withDensity_eq_integral_smul hf.measurable_mk _
    _ = ∫ x, f x • g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]

/--
theorem `integral_withDensity_eq_integral_toReal_smul₀` / 定理 `integral_withDensity_eq_integral_toReal_smul₀`

English:
theorem integral_withDensity_eq_integral_toReal_smul₀
  statement: {f : X -> Real>=0∞} (f_meas : AEMeasurable f μ)
  proof: by
  dsimp only [ENNReal.toReal, ← NNReal.smul_def]
  rw [← integral_withDensity_eq_integral_smul₀ f_meas.ennreal_toNNReal]; rw [withDensity_congr_ae (coe_toNNReal_ae_eq hf_lt_top)]

中文:
定理 integral_withDensity_eq_integral_toReal_smul₀
  结论: {f : X -> 实数>=0∞} (f_meas : AEMeasurable f μ)
  证明: by
  dsimp only [ENNReal.toReal, ← NNReal.smul_def]
  rw [← integral_withDensity_eq_integral_smul₀ f_meas.ennreal_toNNReal]; rw [withDensity_congr_ae (coe_toNNReal_ae_eq hf_lt_top)]

Depends on / 依赖: ENNReal, ENNReal.toReal, NNReal, NNReal.smul_def, coe_toNNReal_ae_eq, ennreal_toNNReal, f_meas, f_meas.ennreal_toNNReal, hf_lt_top, smul_def, toReal, withDensity_congr_ae
-/
theorem integral_withDensity_eq_integral_toReal_smul₀ {f : X -> Real>=0∞} (f_meas : AEMeasurable f μ)
    (hf_lt_top : forallᵐ x ∂μ, f x < ∞) (g : X -> E) :
    ∫ x, g x ∂μ.withDensity f = ∫ x, (f x).toReal • g x ∂μ := by
  dsimp only [ENNReal.toReal, ← NNReal.smul_def]
  rw [← integral_withDensity_eq_integral_smul₀ f_meas.ennreal_toNNReal]; rw [withDensity_congr_ae (coe_toNNReal_ae_eq hf_lt_top)]

/--
theorem `integral_withDensity_eq_integral_toReal_smul` / 定理 `integral_withDensity_eq_integral_toReal_smul`

English:
theorem integral_withDensity_eq_integral_toReal_smul
  statement: {f : X -> Real>=0∞} (f_meas : Measurable f)
  proof: integral_withDensity_eq_integral_toReal_smul₀ f_meas.aemeasurable hf_lt_top g

中文:
定理 integral_withDensity_eq_integral_toReal_smul
  结论: {f : X -> 实数>=0∞} (f_meas : Measurable f)
  证明: integral_withDensity_eq_integral_toReal_smul₀ f_meas.aemeasurable hf_lt_top g

Depends on / 依赖: aemeasurable, f_meas, f_meas.aemeasurable, hf_lt_top
-/
theorem integral_withDensity_eq_integral_toReal_smul {f : X -> Real>=0∞} (f_meas : Measurable f)
    (hf_lt_top : forallᵐ x ∂μ, f x < ∞) (g : X -> E) :
    ∫ x, g x ∂μ.withDensity f = ∫ x, (f x).toReal • g x ∂μ :=
  integral_withDensity_eq_integral_toReal_smul₀ f_meas.aemeasurable hf_lt_top g

/--
theorem `setIntegral_withDensity_eq_setIntegral_smul₀` / 定理 `setIntegral_withDensity_eq_setIntegral_smul₀`

English:
theorem setIntegral_withDensity_eq_setIntegral_smul₀
  statement: {f : X -> Real>=0} {s : Set X}
  proof: by
  rw [restrict_withDensity hs]; rw [integral_withDensity_eq_integral_smul₀ hf]

中文:
定理 setIntegral_withDensity_eq_setIntegral_smul₀
  结论: {f : X -> 实数>=0} {s : Set X}
  证明: by
  rw [restrict_withDensity hs]; rw [integral_withDensity_eq_integral_smul₀ hf]

Depends on / 依赖: restrict_withDensity
-/
theorem setIntegral_withDensity_eq_setIntegral_smul₀ {f : X -> Real>=0} {s : Set X}
    (hf : AEMeasurable f (μ.restrict s)) (g : X -> E) (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ := by
  rw [restrict_withDensity hs]; rw [integral_withDensity_eq_integral_smul₀ hf]

/--
theorem `setIntegral_withDensity_eq_setIntegral_toReal_smul₀` / 定理 `setIntegral_withDensity_eq_setIntegral_toReal_smul₀`

English:
theorem setIntegral_withDensity_eq_setIntegral_toReal_smul₀
  statement: {f : X -> Real>=0∞} {s : Set X}
  proof: by
  rw [restrict_withDensity hs]; rw [integral_withDensity_eq_integral_toReal_smul₀ hf hf_top]

中文:
定理 setIntegral_withDensity_eq_setIntegral_toReal_smul₀
  结论: {f : X -> 实数>=0∞} {s : Set X}
  证明: by
  rw [restrict_withDensity hs]; rw [integral_withDensity_eq_integral_toReal_smul₀ hf hf_top]

Depends on / 依赖: hf_top, restrict_withDensity
-/
theorem setIntegral_withDensity_eq_setIntegral_toReal_smul₀ {f : X -> Real>=0∞} {s : Set X}
    (hf : AEMeasurable f (μ.restrict s)) (hf_top : forallᵐ x ∂μ.restrict s, f x < ∞) (g : X -> E)
    (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, (f x).toReal • g x ∂μ := by
  rw [restrict_withDensity hs]; rw [integral_withDensity_eq_integral_toReal_smul₀ hf hf_top]

/--
theorem `setIntegral_withDensity_eq_setIntegral_smul` / 定理 `setIntegral_withDensity_eq_setIntegral_smul`

English:
theorem setIntegral_withDensity_eq_setIntegral_smul
  statement: {f : X -> Real>=0} (f_meas : Measurable f)
  proof: setIntegral_withDensity_eq_setIntegral_smul₀ f_meas.aemeasurable _ hs

中文:
定理 setIntegral_withDensity_eq_setIntegral_smul
  结论: {f : X -> 实数>=0} (f_meas : Measurable f)
  证明: setIntegral_withDensity_eq_setIntegral_smul₀ f_meas.aemeasurable _ hs

Depends on / 依赖: aemeasurable, f_meas, f_meas.aemeasurable
-/
theorem setIntegral_withDensity_eq_setIntegral_smul {f : X -> Real>=0} (f_meas : Measurable f)
    (g : X -> E) {s : Set X} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ :=
  setIntegral_withDensity_eq_setIntegral_smul₀ f_meas.aemeasurable _ hs

/--
theorem `setIntegral_withDensity_eq_setIntegral_toReal_smul` / 定理 `setIntegral_withDensity_eq_setIntegral_toReal_smul`

English:
theorem setIntegral_withDensity_eq_setIntegral_toReal_smul
  statement: {f : X -> Real>=0∞} {s : Set X}
  proof: setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hf.aemeasurable hf_top g hs

中文:
定理 setIntegral_withDensity_eq_setIntegral_toReal_smul
  结论: {f : X -> 实数>=0∞} {s : Set X}
  证明: setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hf.aemeasurable hf_top g hs

Depends on / 依赖: aemeasurable, hf.aemeasurable, hf_top
-/
theorem setIntegral_withDensity_eq_setIntegral_toReal_smul {f : X -> Real>=0∞} {s : Set X}
    (hf : Measurable f) (hf_top : forallᵐ x ∂μ.restrict s, f x < ∞) (g : X -> E) (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, (f x).toReal • g x ∂μ :=
  setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hf.aemeasurable hf_top g hs

/--
theorem `setIntegral_withDensity_eq_setIntegral_smul₀'` / 定理 `setIntegral_withDensity_eq_setIntegral_smul₀'`

English:
theorem setIntegral_withDensity_eq_setIntegral_smul₀'
  statement: [SFinite μ] {f : X -> Real>=0} (s : Set X)
  proof: by
  rw [restrict_withDensity' s]; rw [integral_withDensity_eq_integral_smul₀ hf]

中文:
定理 setIntegral_withDensity_eq_setIntegral_smul₀'
  结论: [SFinite μ] {f : X -> 实数>=0} (s : Set X)
  证明: by
  rw [restrict_withDensity' s]; rw [integral_withDensity_eq_integral_smul₀ hf]

Depends on / 依赖: restrict_withDensity
-/
theorem setIntegral_withDensity_eq_setIntegral_smul₀' [SFinite μ] {f : X -> Real>=0} (s : Set X)
    (hf : AEMeasurable f (μ.restrict s)) (g : X -> E) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ := by
  rw [restrict_withDensity' s]; rw [integral_withDensity_eq_integral_smul₀ hf]

/--
theorem `setIntegral_withDensity_eq_setIntegral_toReal_smul₀'` / 定理 `setIntegral_withDensity_eq_setIntegral_toReal_smul₀'`

English:
theorem setIntegral_withDensity_eq_setIntegral_toReal_smul₀'
  statement: [SFinite μ] {f : X -> Real>=0∞} (s : Set X)
  proof: by
  rw [restrict_withDensity' s]; rw [integral_withDensity_eq_integral_toReal_smul₀ hf hf_top]

中文:
定理 setIntegral_withDensity_eq_setIntegral_toReal_smul₀'
  结论: [SFinite μ] {f : X -> 实数>=0∞} (s : Set X)
  证明: by
  rw [restrict_withDensity' s]; rw [integral_withDensity_eq_integral_toReal_smul₀ hf hf_top]

Depends on / 依赖: hf_top, restrict_withDensity
-/
theorem setIntegral_withDensity_eq_setIntegral_toReal_smul₀' [SFinite μ] {f : X -> Real>=0∞} (s : Set X)
    (hf : AEMeasurable f (μ.restrict s)) (hf_top : forallᵐ x ∂μ.restrict s, f x < ∞) (g : X -> E) :
    ∫ x in s, g x ∂μ.withDensity f = ∫ x in s, (f x).toReal • g x ∂μ := by
  rw [restrict_withDensity' s]; rw [integral_withDensity_eq_integral_toReal_smul₀ hf hf_top]

/--
theorem `setIntegral_withDensity_eq_setIntegral_toReal_smul'` / 定理 `setIntegral_withDensity_eq_setIntegral_toReal_smul'`

English:
theorem setIntegral_withDensity_eq_setIntegral_toReal_smul'
  statement: [SFinite μ] {f : X -> Real>=0∞} (s : Set X)
  proof: setIntegral_withDensity_eq_setIntegral_toReal_smul₀' s hf.aemeasurable hf_top g

中文:
定理 setIntegral_withDensity_eq_setIntegral_toReal_smul'
  结论: [SFinite μ] {f : X -> 实数>=0∞} (s : Set X)
  证明: setIntegral_withDensity_eq_setIntegral_toReal_smul₀' s hf.aemeasurable hf_top g

Depends on / 依赖: aemeasurable, hf.aemeasurable, hf_top
-/
theorem setIntegral_withDensity_eq_setIntegral_toReal_smul' [SFinite μ] {f : X -> Real>=0∞} (s : Set X)
    (hf : Measurable f) (hf_top : forallᵐ x ∂μ.restrict s, f x < ∞) (g : X -> E) :
    ∫ x in s, g x ∂μ.withDensity f = ∫ x in s, (f x).toReal • g x ∂μ :=
  setIntegral_withDensity_eq_setIntegral_toReal_smul₀' s hf.aemeasurable hf_top g
