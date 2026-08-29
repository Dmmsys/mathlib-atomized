/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Dirac deltas as probability measures and embedding of a space into probability measures on it

## Main definitions
* `diracProba`: The Dirac delta mass at a point as a probability measure.

## Main results
* `isEmbedding_diracProba`: If `X` is a completely regular T0 space with its Borel sigma algebra,
  then the mapping that takes a point `x : X` to the delta-measure `diracProba x` is an embedding
  `X ↪ ProbabilityMeasure X`.

## Tags
probability measure, Dirac delta, embedding
-/

@[expose] public section

open Topology Metric Filter Set ENNReal NNReal BoundedContinuousFunction

open scoped Topology ENNReal NNReal BoundedContinuousFunction

/--
lemma `CompletelyRegularSpace.exists_BCNN` / 引理 `CompletelyRegularSpace.exists_BCNN`

English:
lemma CompletelyRegularSpace.exists_BCNN
  statement: {X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X]
  proof: by
  obtain ⟨g, g_cont, gx_zero, g_one_on_K⟩ :=
    CompletelyRegularSpace.completely_regular x K K_closed x_notin_K
  have g_bdd : forall x y, dist (Real.toNNReal (g x)) (Real.toNNReal (g y)) <= 1 := by
    refine fun x y => ((Real.lipschitzWith_toNNReal).dist_le_mul (g x) (g y)).trans ?_
    simpa using Real.dist_le_of_mem_Icc_01 (g x).prop (g y).prop
  set g' := BoundedContinuousFunction.mkOfBound
      ⟨fun x => Real.toNNReal (g x), continuous_real_toNNReal.comp g_cont.subtype_val⟩ 1 g_bdd
  set f := 1 - g'
  refine ⟨f, by simp [f, g', gx_zero], fun y y_in_K => by simp [f, g', g_one_on_K y_in_K, tsub_self]⟩

中文:
引理 余mpletelyRegular空间.存在_BCNN
  结论: {X : 类型} [拓扑空间 X] [余mpletelyRegular空间 X]
  证明: by
  obtain ⟨g, g_cont, gx_zero, g_one_on_K⟩ :=
    CompletelyRegularSpace.completely_regular x K K_closed x_notin_K
  have g_bdd : forall x y, dist (Real.toNNReal (g x)) (Real.toNNReal (g y)) <= 1 := by
    refine fun x y => ((Real.lipschitzWith_toNNReal).dist_le_mul (g x) (g y)).trans ?_
    simpa using Real.dist_le_of_mem_Icc_01 (g x).prop (g y).prop
  set g' := BoundedContinuousFunction.mkOfBound
      ⟨fun x => Real.toNNReal (g x), continuous_real_toNNReal.comp g_cont.subtype_val⟩ 1 g_bdd
  set f := 1 - g'
  refine ⟨f, by simp [f, g', gx_zero], fun y y_in_K => by simp [f, g', g_one_on_K y_in_K, tsub_self]⟩

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.mkOfBound, CompletelyRegularSpace, CompletelyRegularSpace.completely_regular, K_closed, Real.dist_le_of_mem_Icc_01, Real.lipschitzWith_toNNReal, Real.toNNReal, completely_regular, continuous_real_toNNReal, continuous_real_toNNReal.comp, dist_le_mul, dist_le_of_mem_Icc_01, g_bdd, g_cont, g_cont.subtype_val, g_one_on_K, gx_zero, lipschitzWith_toNNReal, mkOfBound
-/
lemma CompletelyRegularSpace.exists_BCNN {X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X]
    {K : Set X} (K_closed : IsClosed K) {x : X} (x_notin_K : x ∉ K) :
    exists (f : X ->ᵇ Real>=0), f x = 1 ∧ (forall y in K, f y = 0) := by
  obtain ⟨g, g_cont, gx_zero, g_one_on_K⟩ :=
    CompletelyRegularSpace.completely_regular x K K_closed x_notin_K
  have g_bdd : forall x y, dist (Real.toNNReal (g x)) (Real.toNNReal (g y)) <= 1 := by
    refine fun x y => ((Real.lipschitzWith_toNNReal).dist_le_mul (g x) (g y)).trans ?_
    simpa using Real.dist_le_of_mem_Icc_01 (g x).prop (g y).prop
  set g' := BoundedContinuousFunction.mkOfBound
      ⟨fun x => Real.toNNReal (g x), continuous_real_toNNReal.comp g_cont.subtype_val⟩ 1 g_bdd
  set f := 1 - g'
  refine ⟨f, by simp [f, g', gx_zero], fun y y_in_K => by simp [f, g', g_one_on_K y_in_K, tsub_self]⟩

namespace MeasureTheory

section embed_to_probabilityMeasure

variable {X : Type*} [MeasurableSpace X]

/--
Definition of `diracProba` / `diracProba` 的定义

English:
definition diracProba
  signature: (x : X)
  body: ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩

中文:
定义 diracProba
  签名: (x : X)
  定义体: ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩

Depends on / 依赖: Measure, Measure.dirac, Measure.dirac.isProbabilityMeasure, isProbabilityMeasure
-/
noncomputable def diracProba (x : X) : ProbabilityMeasure X :=
  ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩

/--
lemma `injective_diracProba` / 引理 `injective_diracProba`

English:
lemma injective_diracProba
  given: {X : Type*} [MeasurableSpace X] [MeasurableSpace.SeparatesPoints X]
  proof: by
  intro x y x_eq_y
  simpa [diracProba, dirac_eq_dirac_iff] using congr(ProbabilityMeasure.toMeasure $x_eq_y)

中文:
引理 injective_diracProba
  条件: {X : 类型} [可测空间 X] [可测空间.SeparatesPoints X]
  证明: by
  intro x y x_eq_y
  simpa [diracProba, dirac_eq_dirac_iff] using congr(ProbabilityMeasure.toMeasure $x_eq_y)

Depends on / 依赖: ProbabilityMeasure, ProbabilityMeasure.toMeasure, diracProba, dirac_eq_dirac_iff, toMeasure, x_eq_y
-/
lemma injective_diracProba {X : Type*} [MeasurableSpace X] [MeasurableSpace.SeparatesPoints X] :
    Function.Injective (fun (x : X) => diracProba x) := by
  intro x y x_eq_y
  simpa [diracProba, dirac_eq_dirac_iff] using congr(ProbabilityMeasure.toMeasure $x_eq_y)

/--
lemma `diracProba_toMeasure_apply'` / 引理 `diracProba_toMeasure_apply'`

English:
lemma diracProba_toMeasure_apply'
  given: (x : X) {A : Set X} (A_mble : MeasurableSet A)
  proof: Measure.dirac_apply' x A_mble

中文:
引理 diracProba_toMeasure_apply'
  条件: (x : X) {A : 集合 X} (A_mble : 可测集 A)
  证明: Measure.dirac_apply' x A_mble
-/
@[simp] lemma diracProba_toMeasure_apply' (x : X) {A : Set X} (A_mble : MeasurableSet A) :
    (diracProba x).toMeasure A = A.indicator 1 x := Measure.dirac_apply' x A_mble

/--
lemma `diracProba_toMeasure_apply_of_mem` / 引理 `diracProba_toMeasure_apply_of_mem`

English:
lemma diracProba_toMeasure_apply_of_mem
  given: {x : X} {A : Set X} (x_in_A : x in A)
  proof: Measure.dirac_apply_of_mem x_in_A

中文:
引理 diracProba_toMeasure_apply_of_mem
  条件: {x : X} {A : 集合 X} (x_in_A : x in A)
  证明: Measure.dirac_apply_of_mem x_in_A
-/
@[simp] lemma diracProba_toMeasure_apply_of_mem {x : X} {A : Set X} (x_in_A : x in A) :
    (diracProba x).toMeasure A = 1 := Measure.dirac_apply_of_mem x_in_A

/--
lemma `diracProba_toMeasure_apply` / 引理 `diracProba_toMeasure_apply`

English:
lemma diracProba_toMeasure_apply
  given: [MeasurableSingletonClass X] (x : X) (A : Set X)
  proof: Measure.dirac_apply _ _

中文:
引理 diracProba_toMeasure_apply
  条件: [MeasurableSingleton类 X] (x : X) (A : 集合 X)
  证明: Measure.dirac_apply _ _
-/
@[simp] lemma diracProba_toMeasure_apply [MeasurableSingletonClass X] (x : X) (A : Set X) :
    (diracProba x).toMeasure A = A.indicator 1 x := Measure.dirac_apply _ _

variable [TopologicalSpace X] [OpensMeasurableSpace X]

/--
lemma `continuous_diracProba` / 引理 `continuous_diracProba`

English:
lemma continuous_diracProba
  statement: Continuous (fun (x : X) => diracProba x)
  proof: by
  rw [continuous_iff_continuousAt]
  apply fun x => ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mpr fun f => ?_
  have f_mble : Measurable (fun X => (f X : Real>=0∞)) :=
    measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable
  simp only [diracProba, ProbabilityMeasure.coe_mk, lintegral_dirac' _ f_mble]
  exact (ENNReal.continuous_coe.comp f.continuous).continuousAt

中文:
引理 continuous_diracProba
  结论: 连续 (fun (x : X) => diracProba x)
  证明: by
  rw [continuous_iff_continuousAt]
  apply fun x => ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mpr fun f => ?_
  have f_mble : Measurable (fun X => (f X : Real>=0∞)) :=
    measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable
  simp only [diracProba, ProbabilityMeasure.coe_mk, lintegral_dirac' _ f_mble]
  exact (ENNReal.continuous_coe.comp f.continuous).continuousAt

Depends on / 依赖: ENNReal, ENNReal.continuous_coe.comp, Measurable, ProbabilityMeasure, ProbabilityMeasure.coe_mk, ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mpr, coe_mk, continuous, continuousAt, continuous_coe, continuous_iff_continuousAt, diracProba, f.continuous, f.continuous.measurable, f_mble, lintegral_dirac, measurable, measurable_coe_nnreal_ennreal_iff, measurable_coe_nnreal_ennreal_iff.mpr, tendsto_iff_forall_lintegral_tendsto
-/
lemma continuous_diracProba : Continuous (fun (x : X) => diracProba x) := by
  rw [continuous_iff_continuousAt]
  apply fun x => ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mpr fun f => ?_
  have f_mble : Measurable (fun X => (f X : Real>=0∞)) :=
    measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable
  simp only [diracProba, ProbabilityMeasure.coe_mk, lintegral_dirac' _ f_mble]
  exact (ENNReal.continuous_coe.comp f.continuous).continuousAt

/--
lemma `not_tendsto_diracProba_of_not_tendsto` / 引理 `not_tendsto_diracProba_of_not_tendsto`

English:
lemma not_tendsto_diracProba_of_not_tendsto
  statement: [CompletelyRegularSpace X] {x : X} (L : Filter X)
  proof: by
  obtain ⟨U, U_nhds, hU⟩ : exists U, U in 𝓝 x ∧ existsᶠ x in L, x ∉ U := by
    contrapose! h
    exact h
  have Uint_nhds : interior U in 𝓝 x := by simpa only [interior_mem_nhds] using U_nhds
  obtain ⟨f, fx_eq_one, f_vanishes_outside⟩ :=
    CompletelyRegularSpace.exists_BCNN isOpen_interior.isClosed_compl
      (by simpa only [mem_compl_iff, not_not] using mem_of_mem_nhds Uint_nhds)
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto]; rw [not_forall]
  use f
  simp only [diracProba, ProbabilityMeasure.coe_mk, fx_eq_one,
             lintegral_dirac' _ (measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable)]
  apply not_tendsto_iff_exists_frequently_notMem.mpr
  refine ⟨Ioi 0, Ioi_mem_nhds (by simp only [ENNReal.coe_one, zero_lt_one]),
          hU.mp (Eventually.of_forall ?_)⟩
  intro x x_notin_U
  rw [f_vanishes_outside x (compl_subset_compl.mpr interior_subset x_notin_U)]
  simp only [ENNReal.coe_zero, mem_Ioi, lt_self_iff_false, not_false_eq_true]

中文:
引理 not_tendsto_diracProba_of_not_tendsto
  结论: [余mpletelyRegular空间 X] {x : X} (L : 滤子 X)
  证明: by
  obtain ⟨U, U_nhds, hU⟩ : exists U, U in 𝓝 x ∧ existsᶠ x in L, x ∉ U := by
    contrapose! h
    exact h
  have Uint_nhds : interior U in 𝓝 x := by simpa only [interior_mem_nhds] using U_nhds
  obtain ⟨f, fx_eq_one, f_vanishes_outside⟩ :=
    CompletelyRegularSpace.exists_BCNN isOpen_interior.isClosed_compl
      (by simpa only [mem_compl_iff, not_not] using mem_of_mem_nhds Uint_nhds)
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto]; rw [not_forall]
  use f
  simp only [diracProba, ProbabilityMeasure.coe_mk, fx_eq_one,
             lintegral_dirac' _ (measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable)]
  apply not_tendsto_iff_exists_frequently_notMem.mpr
  refine ⟨Ioi 0, Ioi_mem_nhds (by simp only [ENNReal.coe_one, zero_lt_one]),
          hU.mp (Eventually.of_forall ?_)⟩
  intro x x_notin_U
  rw [f_vanishes_outside x (compl_subset_compl.mpr interior_subset x_notin_U)]
  simp only [ENNReal.coe_zero, mem_Ioi, lt_self_iff_false, not_false_eq_true]

Depends on / 依赖: CompletelyRegularSpace, CompletelyRegularSpace.exists_BCNN, ProbabilityMeasure, ProbabilityMeasure.coe_mk, ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto, U_nhds, Uint_nhds, coe_mk, contrapose, diracProba, exists_BCNN, f_vanishes_outside, fx_eq_one, interior, interior_mem_nhds, isClosed_compl, isOpen_interior, isOpen_interior.isClosed_compl, mem_compl_iff, mem_of_mem_nhds
-/
lemma not_tendsto_diracProba_of_not_tendsto [CompletelyRegularSpace X] {x : X} (L : Filter X)
    (h : ¬ Tendsto id L (𝓝 x)) :
    ¬ Tendsto diracProba L (𝓝 (diracProba x)) := by
  obtain ⟨U, U_nhds, hU⟩ : exists U, U in 𝓝 x ∧ existsᶠ x in L, x ∉ U := by
    contrapose! h
    exact h
  have Uint_nhds : interior U in 𝓝 x := by simpa only [interior_mem_nhds] using U_nhds
  obtain ⟨f, fx_eq_one, f_vanishes_outside⟩ :=
    CompletelyRegularSpace.exists_BCNN isOpen_interior.isClosed_compl
      (by simpa only [mem_compl_iff, not_not] using mem_of_mem_nhds Uint_nhds)
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto]; rw [not_forall]
  use f
  simp only [diracProba, ProbabilityMeasure.coe_mk, fx_eq_one,
             lintegral_dirac' _ (measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable)]
  apply not_tendsto_iff_exists_frequently_notMem.mpr
  refine ⟨Ioi 0, Ioi_mem_nhds (by simp only [ENNReal.coe_one, zero_lt_one]),
          hU.mp (Eventually.of_forall ?_)⟩
  intro x x_notin_U
  rw [f_vanishes_outside x (compl_subset_compl.mpr interior_subset x_notin_U)]
  simp only [ENNReal.coe_zero, mem_Ioi, lt_self_iff_false, not_false_eq_true]

/--
lemma `tendsto_diracProba_iff_tendsto` / 引理 `tendsto_diracProba_iff_tendsto`

English:
lemma tendsto_diracProba_iff_tendsto
  given: [CompletelyRegularSpace X] {x : X} (L : Filter X)
  proof: by
  constructor
  · contrapose
    exact not_tendsto_diracProba_of_not_tendsto L
  · intro h
    have aux := (@continuous_diracProba X _ _ _).continuousAt (x := x)
    simp only [ContinuousAt] at aux
    exact aux.comp h

中文:
引理 tendsto_diracProba_iff_tendsto
  条件: [余mpletelyRegular空间 X] {x : X} (L : 滤子 X)
  证明: by
  constructor
  · contrapose
    exact not_tendsto_diracProba_of_not_tendsto L
  · intro h
    have aux := (@continuous_diracProba X _ _ _).continuousAt (x := x)
    simp only [ContinuousAt] at aux
    exact aux.comp h

Depends on / 依赖: ContinuousAt, aux.comp, continuousAt, continuous_diracProba, contrapose, not_tendsto_diracProba_of_not_tendsto
-/
lemma tendsto_diracProba_iff_tendsto [CompletelyRegularSpace X] {x : X} (L : Filter X) :
    Tendsto diracProba L (𝓝 (diracProba x)) ↔ Tendsto id L (𝓝 x) := by
  constructor
  · contrapose
    exact not_tendsto_diracProba_of_not_tendsto L
  · intro h
    have aux := (@continuous_diracProba X _ _ _).continuousAt (x := x)
    simp only [ContinuousAt] at aux
    exact aux.comp h

/--
Definition of `diracProbaInverse` / `diracProbaInverse` 的定义

English:
definition diracProbaInverse
  signature: : range (diracProba (X := X)) -> X
  body: fun μ' => (mem_range.mp μ'.prop).choose

中文:
定义 diracProbaInverse
  签名: : range (diracProba (X := X)) -> X
  定义体: fun μ' => (mem_range.mp μ'.prop).choose
-/
noncomputable def diracProbaInverse : range (diracProba (X := X)) -> X :=
  fun μ' => (mem_range.mp μ'.prop).choose

-- We redeclare `X` here to temporarily avoid the `[TopologicalSpace X]` instance.
/--
lemma `diracProba_diracProbaInverse` / 引理 `diracProba_diracProbaInverse`

English:
lemma diracProba_diracProbaInverse
  statement: {X : Type*} [MeasurableSpace X]
  proof: (mem_range.mp μ.prop).choose_spec

中文:
引理 diracProba_diracProbaInverse
  结论: {X : 类型} [可测空间 X]
  证明: (mem_range.mp μ.prop).choose_spec
-/
@[simp] lemma diracProba_diracProbaInverse {X : Type*} [MeasurableSpace X]
    (μ : range (diracProba (X := X))) :
    diracProba (diracProbaInverse μ) = μ := (mem_range.mp μ.prop).choose_spec

/--
lemma `diracProbaInverse_eq` / 引理 `diracProbaInverse_eq`

English:
lemma diracProbaInverse_eq
  statement: [T0Space X] {x : X} {μ : range (diracProba (X := X))}
  proof: by
  apply injective_diracProba (X := X)
  simp only [← h]
  exact (mem_range.mp μ.prop).choose_spec

中文:
引理 diracProbaInverse_eq
  结论: [T0空间 X] {x : X} {μ : range (diracProba (X := X))}
  证明: by
  apply injective_diracProba (X := X)
  simp only [← h]
  exact (mem_range.mp μ.prop).choose_spec
-/
lemma diracProbaInverse_eq [T0Space X] {x : X} {μ : range (diracProba (X := X))}
    (h : μ = diracProba x) :
    diracProbaInverse μ = x := by
  apply injective_diracProba (X := X)
  simp only [← h]
  exact (mem_range.mp μ.prop).choose_spec

/--
Definition of `diracProbaEquiv` / `diracProbaEquiv` 的定义

English:
definition diracProbaEquiv
  signature: [T0Space X]
  body: fun x => ⟨diracProba x, by exact mem_range_self x⟩
  invFun := diracProbaInverse
  left_inv x := by apply diracProbaInverse_eq; rfl
  right_inv μ := Subtype.ext (by simp only [diracProba_diracProbaInverse])

中文:
定义 diracProbaEquiv
  签名: [T0空间 X]
  定义体: fun x => ⟨diracProba x, by exact mem_range_self x⟩
  invFun := diracProbaInverse
  left_inv x := by apply diracProbaInverse_eq; rfl
  right_inv μ := Subtype.ext (by simp only [diracProba_diracProbaInverse])
-/
noncomputable def diracProbaEquiv [T0Space X] : X ≃ range (diracProba (X := X)) where
  toFun := fun x => ⟨diracProba x, by exact mem_range_self x⟩
  invFun := diracProbaInverse
  left_inv x := by apply diracProbaInverse_eq; rfl
  right_inv μ := Subtype.ext (by simp only [diracProba_diracProbaInverse])

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `diracProba_comp_diracProbaEquiv_symm_eq_val` / 引理 `diracProba_comp_diracProbaEquiv_symm_eq_val`

English:
lemma diracProba_comp_diracProbaEquiv_symm_eq_val
  given: [T0Space X]
  proof: by
  funext μ; simp [diracProbaEquiv]

中文:
引理 diracProba_comp_diracProbaEquiv_symm_eq_val
  条件: [T0空间 X]
  证明: by
  funext μ; simp [diracProbaEquiv]

Depends on / 依赖: diracProbaEquiv
-/
lemma diracProba_comp_diracProbaEquiv_symm_eq_val [T0Space X] :
    diracProba ∘ (diracProbaEquiv (X := X)).symm = fun μ => μ.val := by
  funext μ; simp [diracProbaEquiv]

/--
lemma `tendsto_diracProbaEquivSymm_iff_tendsto` / 引理 `tendsto_diracProbaEquivSymm_iff_tendsto`

English:
lemma tendsto_diracProbaEquivSymm_iff_tendsto
  statement: [T0Space X] [CompletelyRegularSpace X]
  proof: by
  have key :=
    tendsto_diracProba_iff_tendsto (F.map diracProbaEquiv.symm) (x := diracProbaEquiv.symm μ)
  rw [← (diracProbaEquiv (X := X)).symm_comp_self]; rw [← tendsto_map'_iff] at key
  simp only [tendsto_map'_iff, map_map, Equiv.self_comp_symm, map_id] at key
  simp only [← key, diracProba_comp_diracProbaEquiv_symm_eq_val]
  convert! tendsto_subtype_rng.symm
  exact apply_rangeSplitting (fun x => diracProba x) μ

中文:
引理 tendsto_diracProbaEquivSymm_iff_tendsto
  结论: [T0空间 X] [余mpletelyRegular空间 X]
  证明: by
  have key :=
    tendsto_diracProba_iff_tendsto (F.map diracProbaEquiv.symm) (x := diracProbaEquiv.symm μ)
  rw [← (diracProbaEquiv (X := X)).symm_comp_self]; rw [← tendsto_map'_iff] at key
  simp only [tendsto_map'_iff, map_map, Equiv.self_comp_symm, map_id] at key
  simp only [← key, diracProba_comp_diracProbaEquiv_symm_eq_val]
  convert! tendsto_subtype_rng.symm
  exact apply_rangeSplitting (fun x => diracProba x) μ

Depends on / 依赖: Filter, diracProba
-/
lemma tendsto_diracProbaEquivSymm_iff_tendsto [T0Space X] [CompletelyRegularSpace X]
    {μ : range (diracProba (X := X))} (F : Filter (range (diracProba (X := X)))) :
    Tendsto diracProbaEquiv.symm F (𝓝 (diracProbaEquiv.symm μ)) ↔ Tendsto id F (𝓝 μ) := by
  have key :=
    tendsto_diracProba_iff_tendsto (F.map diracProbaEquiv.symm) (x := diracProbaEquiv.symm μ)
  rw [← (diracProbaEquiv (X := X)).symm_comp_self]; rw [← tendsto_map'_iff] at key
  simp only [tendsto_map'_iff, map_map, Equiv.self_comp_symm, map_id] at key
  simp only [← key, diracProba_comp_diracProbaEquiv_symm_eq_val]
  convert! tendsto_subtype_rng.symm
  exact apply_rangeSplitting (fun x => diracProba x) μ

/--
lemma `continuous_diracProbaEquiv` / 引理 `continuous_diracProbaEquiv`

English:
lemma continuous_diracProbaEquiv
  given: [T0Space X]
  proof: Continuous.subtype_mk continuous_diracProba mem_range_self

中文:
引理 continuous_diracProbaEquiv
  条件: [T0空间 X]
  证明: Continuous.subtype_mk continuous_diracProba mem_range_self
-/
lemma continuous_diracProbaEquiv [T0Space X] :
    Continuous (diracProbaEquiv (X := X)) :=
  Continuous.subtype_mk continuous_diracProba mem_range_self

/--
lemma `continuous_diracProbaEquivSymm` / 引理 `continuous_diracProbaEquivSymm`

English:
lemma continuous_diracProbaEquivSymm
  given: [T0Space X] [CompletelyRegularSpace X]
  proof: by
  apply continuous_iff_continuousAt.mpr
  intro μ
  apply continuousAt_of_tendsto_nhds (y := diracProbaInverse μ)
  exact (tendsto_diracProbaEquivSymm_iff_tendsto _).mpr fun _ mem_nhds => mem_nhds

中文:
引理 continuous_diracProbaEquivSymm
  条件: [T0空间 X] [余mpletelyRegular空间 X]
  证明: by
  apply continuous_iff_continuousAt.mpr
  intro μ
  apply continuousAt_of_tendsto_nhds (y := diracProbaInverse μ)
  exact (tendsto_diracProbaEquivSymm_iff_tendsto _).mpr fun _ mem_nhds => mem_nhds

Depends on / 依赖: continuousAt_of_tendsto_nhds, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, diracProbaInverse, mem_nhds, tendsto_diracProbaEquivSymm_iff_tendsto
-/
lemma continuous_diracProbaEquivSymm [T0Space X] [CompletelyRegularSpace X] :
    Continuous (diracProbaEquiv (X := X)).symm := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  apply continuousAt_of_tendsto_nhds (y := diracProbaInverse μ)
  exact (tendsto_diracProbaEquivSymm_iff_tendsto _).mpr fun _ mem_nhds => mem_nhds

/--
Definition of `diracProbaHomeomorph` / `diracProbaHomeomorph` 的定义

English:
definition diracProbaHomeomorph
  signature: [T0Space X] [CompletelyRegularSpace X]
  body: @Homeomorph.mk X _ _ _ diracProbaEquiv continuous_diracProbaEquiv continuous_diracProbaEquivSymm

中文:
定义 diracProbaHomeomorph
  签名: [T0空间 X] [余mpletelyRegular空间 X]
  定义体: @Homeomorph.mk X _ _ _ diracProbaEquiv continuous_diracProbaEquiv continuous_diracProbaEquivSymm
-/
noncomputable def diracProbaHomeomorph [T0Space X] [CompletelyRegularSpace X] :
    X ≃ₜ range (diracProba (X := X)) :=
  @Homeomorph.mk X _ _ _ diracProbaEquiv continuous_diracProbaEquiv continuous_diracProbaEquivSymm

/--
theorem `isEmbedding_diracProba` / 定理 `isEmbedding_diracProba`

English:
theorem isEmbedding_diracProba
  given: [T0Space X] [CompletelyRegularSpace X]
  proof: IsEmbedding.subtypeVal.comp diracProbaHomeomorph.isEmbedding

中文:
定理 isEmbedding_diracProba
  条件: [T0空间 X] [余mpletelyRegular空间 X]
  证明: IsEmbedding.subtypeVal.comp diracProbaHomeomorph.isEmbedding

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.comp, diracProbaHomeomorph, diracProbaHomeomorph.isEmbedding, isEmbedding, subtypeVal
-/
theorem isEmbedding_diracProba [T0Space X] [CompletelyRegularSpace X] :
    IsEmbedding (fun (x : X) => diracProba x) :=
  IsEmbedding.subtypeVal.comp diracProbaHomeomorph.isEmbedding

end embed_to_probabilityMeasure

end MeasureTheory
