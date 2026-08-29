/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous functions in Lp space

When `α` is a topological space equipped with a finite Borel measure, there is a bounded linear map
from the normed space of bounded continuous functions (`α →ᵇ E`) to `Lp E p μ`. We construct this
as `BoundedContinuousFunction.toLp`.

-/

@[expose] public section

open BoundedContinuousFunction MeasureTheory Filter
open scoped ENNReal

variable {α E : Type*} {m m0 : MeasurableSpace α} {p : Real>=0∞} {μ : Measure α}
  [TopologicalSpace α] [BorelSpace α] [NormedAddCommGroup E] [SecondCountableTopologyEither α E]

variable (E p μ) in
/--
Definition of `MeasureTheory.Lp.boundedContinuousFunction` / `MeasureTheory.Lp.boundedContinuousFunction` 的定义

English:
definition MeasureTheory.Lp.boundedContinuousFunction
  signature: : AddSubgroup (Lp E p μ)
  body: AddSubgroup.addSubgroupOf
    ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddMonoidHom α E)).range (Lp E p μ)

中文:
定义 MeasureTheory.Lp.boundedContinuousFunction
  签名: : AddSubgroup (Lp E p μ)
  定义体: AddSubgroup.addSubgroupOf
    ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddMonoidHom α E)).range (Lp E p μ)

Depends on / 依赖: AddSubgroup, AddSubgroup.addSubgroupOf, ContinuousMap, ContinuousMap.toAEEqFunAddHom, addSubgroupOf, toAEEqFunAddHom, toContinuousMapAddMonoidHom
-/
noncomputable def MeasureTheory.Lp.boundedContinuousFunction : AddSubgroup (Lp E p μ) :=
  AddSubgroup.addSubgroupOf
    ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddMonoidHom α E)).range (Lp E p μ)

/--
theorem `MeasureTheory.Lp.mem_boundedContinuousFunction_iff` / 定理 `MeasureTheory.Lp.mem_boundedContinuousFunction_iff`

English:
theorem MeasureTheory.Lp.mem_boundedContinuousFunction_iff
  given: {f : Lp E p μ}
  proof: AddSubgroup.mem_addSubgroupOf

中文:
定理 MeasureTheory.Lp.mem_boundedContinuousFunction_iff
  条件: {f : Lp E p μ}
  证明: AddSubgroup.mem_addSubgroupOf

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_addSubgroupOf, mem_addSubgroupOf
-/
theorem MeasureTheory.Lp.mem_boundedContinuousFunction_iff {f : Lp E p μ} :
    f in MeasureTheory.Lp.boundedContinuousFunction E p μ ↔
      exists f₀ : α ->ᵇ E, f₀.toContinuousMap.toAEEqFun μ = (f : α ->ₘ[μ] E) :=
  AddSubgroup.mem_addSubgroupOf

namespace BoundedContinuousFunction

/--
theorem `memLp_top` / 定理 `memLp_top`

English:
theorem memLp_top
  given: (f : α ->ᵇ E)
  statement: MemLp f ⊤ μ
  proof: ⟨by fun_prop, eLpNormEssSup_lt_top_of_ae_bound univ_mem' (id norm_coe_le_norm f)⟩

中文:
定理 memLp_top
  条件: (f : α ->ᵇ E)
  结论: MemLp f ⊤ μ
  证明: ⟨by fun_prop, eLpNormEssSup_lt_top_of_ae_bound univ_mem' (id norm_coe_le_norm f)⟩

Depends on / 依赖: eLpNormEssSup_lt_top_of_ae_bound, fun_prop, norm_coe_le_norm, univ_mem
-/
theorem memLp_top (f : α ->ᵇ E) : MemLp f ⊤ μ :=
⟨by fun_prop, eLpNormEssSup_lt_top_of_ae_bound univ_mem' (id norm_coe_le_norm f)⟩

variable [IsFiniteMeasure μ]

/--
theorem `mem_Lp` / 定理 `mem_Lp`

English:
theorem mem_Lp
  given: (f : α ->ᵇ E)
  statement: f.toContinuousMap.toAEEqFun μ in Lp E p μ
  proof: by
  refine Lp.mem_Lp_of_ae_bound ‖f‖ ?_
  filter_upwards [f.toContinuousMap.coeFn_toAEEqFun μ] with x _
  convert! f.norm_coe_le_norm x using 2

中文:
定理 mem_Lp
  条件: (f : α ->ᵇ E)
  结论: f.toContinuousMap.toAEEqFun μ in Lp E p μ
  证明: by
  refine Lp.mem_Lp_of_ae_bound ‖f‖ ?_
  filter_upwards [f.toContinuousMap.coeFn_toAEEqFun μ] with x _
  convert! f.norm_coe_le_norm x using 2

Depends on / 依赖: Lp.mem_Lp_of_ae_bound, coeFn_toAEEqFun, convert, f.norm_coe_le_norm, f.toContinuousMap.coeFn_toAEEqFun, filter_upwards, mem_Lp_of_ae_bound, norm_coe_le_norm, toContinuousMap
-/
theorem mem_Lp (f : α ->ᵇ E) : f.toContinuousMap.toAEEqFun μ in Lp E p μ := by
  refine Lp.mem_Lp_of_ae_bound ‖f‖ ?_
  filter_upwards [f.toContinuousMap.coeFn_toAEEqFun μ] with x _
  convert! f.norm_coe_le_norm x using 2

/--
theorem `Lp_nnnorm_le` / 定理 `Lp_nnnorm_le`

English:
theorem Lp_nnnorm_le
  given: (f : α ->ᵇ E)
  proof: by
  apply Lp.nnnorm_le_of_ae_bound
  refine (f.toContinuousMap.coeFn_toAEEqFun μ).mono ?_
  intro x hx
  rw [← NNReal.coe_le_coe]; rw [coe_nnnorm]; rw [coe_nnnorm]
  convert! f.norm_coe_le_norm x using 2

中文:
定理 Lp_nnnorm_le
  条件: (f : α ->ᵇ E)
  证明: by
  apply Lp.nnnorm_le_of_ae_bound
  refine (f.toContinuousMap.coeFn_toAEEqFun μ).mono ?_
  intro x hx
  rw [← NNReal.coe_le_coe]; rw [coe_nnnorm]; rw [coe_nnnorm]
  convert! f.norm_coe_le_norm x using 2

Depends on / 依赖: Lp.nnnorm_le_of_ae_bound, NNReal, NNReal.coe_le_coe, coeFn_toAEEqFun, coe_le_coe, coe_nnnorm, convert, f.norm_coe_le_norm, f.toContinuousMap.coeFn_toAEEqFun, nnnorm_le_of_ae_bound, norm_coe_le_norm, toContinuousMap
-/
theorem Lp_nnnorm_le (f : α ->ᵇ E) :
    ‖(⟨f.toContinuousMap.toAEEqFun μ, mem_Lp f⟩ : Lp E p μ)‖₊ <=
      measureUnivNNReal μ ^ p.toReal⁻¹ * ‖f‖₊ := by
  apply Lp.nnnorm_le_of_ae_bound
  refine (f.toContinuousMap.coeFn_toAEEqFun μ).mono ?_
  intro x hx
  rw [← NNReal.coe_le_coe]; rw [coe_nnnorm]; rw [coe_nnnorm]
  convert! f.norm_coe_le_norm x using 2

/--
theorem `Lp_norm_le` / 定理 `Lp_norm_le`

English:
theorem Lp_norm_le
  given: (f : α ->ᵇ E)
  proof: Lp_nnnorm_le f

中文:
定理 Lp_norm_le
  条件: (f : α ->ᵇ E)
  证明: Lp_nnnorm_le f

Depends on / 依赖: Lp_nnnorm_le
-/
theorem Lp_norm_le (f : α ->ᵇ E) :
    ‖(⟨f.toContinuousMap.toAEEqFun μ, mem_Lp f⟩ : Lp E p μ)‖ <=
      measureUnivNNReal μ ^ p.toReal⁻¹ * ‖f‖ :=
  Lp_nnnorm_le f

variable (p μ)

/--
Definition of `toLpHom` / `toLpHom` 的定义

English:
definition toLpHom
  signature: [Fact (1 <= p)]
  body: { AddMonoidHom.codRestrict ((ContinuousMap.toAEEqFunAddHom μ).comp
    (toContinuousMapAddMonoidHom α E)) (Lp E p μ) mem_Lp with
    bound' := ⟨_, Lp_norm_le⟩ }

中文:
定义 toLpHom
  签名: [Fact (1 <= p)]
  定义体: { AddMonoidHom.codRestrict ((ContinuousMap.toAEEqFunAddHom μ).comp
    (toContinuousMapAddMonoidHom α E)) (Lp E p μ) mem_Lp with
    bound' := ⟨_, Lp_norm_le⟩ }

Depends on / 依赖: AddMonoidHom, AddMonoidHom.codRestrict, ContinuousMap, ContinuousMap.toAEEqFunAddHom, Lp_norm_le, codRestrict, mem_Lp, toAEEqFunAddHom, toContinuousMapAddMonoidHom
-/
def toLpHom [Fact (1 <= p)] : NormedAddGroupHom (α ->ᵇ E) (Lp E p μ) :=
  { AddMonoidHom.codRestrict ((ContinuousMap.toAEEqFunAddHom μ).comp
    (toContinuousMapAddMonoidHom α E)) (Lp E p μ) mem_Lp with
    bound' := ⟨_, Lp_norm_le⟩ }

/--
theorem `range_toLpHom` / 定理 `range_toLpHom`

English:
theorem range_toLpHom
  given: [Fact (1 <= p)]
  proof: by
  symm
  exact AddMonoidHom.addSubgroupOf_range_eq_of_le
      ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddMonoidHom α E))
      (by rintro - ⟨f, rfl⟩; exact mem_Lp f : _ <= Lp E p μ)

中文:
定理 range_toLpHom
  条件: [Fact (1 <= p)]
  证明: by
  symm
  exact AddMonoidHom.addSubgroupOf_range_eq_of_le
      ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddMonoidHom α E))
      (by rintro - ⟨f, rfl⟩; exact mem_Lp f : _ <= Lp E p μ)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.addSubgroupOf_range_eq_of_le, ContinuousMap, ContinuousMap.toAEEqFunAddHom, addSubgroupOf_range_eq_of_le, mem_Lp, toAEEqFunAddHom, toContinuousMapAddMonoidHom
-/
theorem range_toLpHom [Fact (1 <= p)] :
    ((toLpHom p μ).range : AddSubgroup (Lp E p μ)) =
      MeasureTheory.Lp.boundedContinuousFunction E p μ := by
  symm
  exact AddMonoidHom.addSubgroupOf_range_eq_of_le
      ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddMonoidHom α E))
      (by rintro - ⟨f, rfl⟩; exact mem_Lp f : _ <= Lp E p μ)

variable (𝕜 : Type*) [Fact (1 <= p)] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/--
Definition of `toLp` / `toLp` 的定义

English:
definition toLp
  signature: : (α ->ᵇ E) ->L[𝕜] Lp E p μ
  body: LinearMap.mkContinuous
    (LinearMap.codRestrict (Lp.LpSubmodule 𝕜 E p μ)
      ((ContinuousMap.toAEEqFunLinearMap μ).comp (toContinuousMapLinearMap α E 𝕜)) mem_Lp)
    _ Lp_norm_le

中文:
定义 toLp
  签名: : (α ->ᵇ E) ->L[𝕜] Lp E p μ
  定义体: LinearMap.mkContinuous
    (LinearMap.codRestrict (Lp.LpSubmodule 𝕜 E p μ)
      ((ContinuousMap.toAEEqFunLinearMap μ).comp (toContinuousMapLinearMap α E 𝕜)) mem_Lp)
    _ Lp_norm_le

Depends on / 依赖: ContinuousMap, ContinuousMap.toAEEqFunLinearMap, LinearMap, LinearMap.codRestrict, LinearMap.mkContinuous, Lp.LpSubmodule, LpSubmodule, Lp_norm_le, codRestrict, mem_Lp, mkContinuous, toAEEqFunLinearMap, toContinuousMapLinearMap
-/
noncomputable def toLp : (α ->ᵇ E) ->L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    (LinearMap.codRestrict (Lp.LpSubmodule 𝕜 E p μ)
      ((ContinuousMap.toAEEqFunLinearMap μ).comp (toContinuousMapLinearMap α E 𝕜)) mem_Lp)
    _ Lp_norm_le

/--
theorem `coeFn_toLp` / 定理 `coeFn_toLp`

English:
theorem coeFn_toLp
  given: (f : α ->ᵇ E)
  proof: AEEqFun.coeFn_mk f _

中文:
定理 coeFn_toLp
  条件: (f : α ->ᵇ E)
  证明: AEEqFun.coeFn_mk f _
-/
theorem coeFn_toLp (f : α ->ᵇ E) :
    toLp (E := E) p μ 𝕜 f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f _

variable {𝕜}

/--
theorem `range_toLp` / 定理 `range_toLp`

English:
theorem range_toLp
  proof: range_toLpHom p μ

中文:
定理 range_toLp
  证明: range_toLpHom p μ

Depends on / 依赖: range_toLpHom
-/
theorem range_toLp :
    (toLp p μ 𝕜 : (α ->ᵇ E) ->L[𝕜] Lp E p μ).range.toAddSubgroup =
      MeasureTheory.Lp.boundedContinuousFunction E p μ :=
  range_toLpHom p μ

variable {p}

/--
theorem `toLp_norm_le` / 定理 `toLp_norm_le`

English:
theorem toLp_norm_le
  given: {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  proof: LinearMap.mkContinuous_norm_le _ (measureUnivNNReal μ ^ p.toReal⁻¹).coe_nonneg _

中文:
定理 toLp_norm_le
  条件: {𝕜 : 类型} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  证明: LinearMap.mkContinuous_norm_le _ (measureUnivNNReal μ ^ p.toReal⁻¹).coe_nonneg _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, coe_nonneg, measureUnivNNReal, mkContinuous_norm_le, p.toReal, toReal
-/
theorem toLp_norm_le {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] :
    ‖(toLp p μ 𝕜 : (α ->ᵇ E) ->L[𝕜] Lp E p μ)‖ <= measureUnivNNReal μ ^ p.toReal⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (measureUnivNNReal μ ^ p.toReal⁻¹).coe_nonneg _

/--
theorem `toLp_inj` / 定理 `toLp_inj`

English:
theorem toLp_inj
  given: {f g : α ->ᵇ E} [μ.IsOpenPosMeasure]
  proof: by
  refine ⟨fun h => ?_, by tauto⟩
  rw [← DFunLike.coe_fn_eq]; rw [← (map_continuous f).ae_eq_iff_eq μ (map_continuous g)]
  refine (coeFn_toLp p μ 𝕜 f).symm.trans (EventuallyEq.trans ?_ <| coeFn_toLp p μ 𝕜 g)
  rw [h]

中文:
定理 toLp_inj
  条件: {f g : α ->ᵇ E} [μ.IsOpenPosMeasure]
  证明: by
  refine ⟨fun h => ?_, by tauto⟩
  rw [← DFunLike.coe_fn_eq]; rw [← (map_continuous f).ae_eq_iff_eq μ (map_continuous g)]
  refine (coeFn_toLp p μ 𝕜 f).symm.trans (EventuallyEq.trans ?_ <| coeFn_toLp p μ 𝕜 g)
  rw [h]

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, EventuallyEq, EventuallyEq.trans, ae_eq_iff_eq, coeFn_toLp, coe_fn_eq, map_continuous, symm.trans
-/
theorem toLp_inj {f g : α ->ᵇ E} [μ.IsOpenPosMeasure] :
    toLp (E := E) p μ 𝕜 f = toLp (E := E) p μ 𝕜 g ↔ f = g := by
  refine ⟨fun h => ?_, by tauto⟩
  rw [← DFunLike.coe_fn_eq]; rw [← (map_continuous f).ae_eq_iff_eq μ (map_continuous g)]
  refine (coeFn_toLp p μ 𝕜 f).symm.trans (EventuallyEq.trans ?_ <| coeFn_toLp p μ 𝕜 g)
  rw [h]

/--
theorem `toLp_injective` / 定理 `toLp_injective`

English:
theorem toLp_injective
  given: [μ.IsOpenPosMeasure]
  proof: fun _f _g hfg => (toLp_inj μ).mp hfg

中文:
定理 toLp_injective
  条件: [μ.IsOpenPosMeasure]
  证明: fun _f _g hfg => (toLp_inj μ).mp hfg

Depends on / 依赖: toLp_inj
-/
theorem toLp_injective [μ.IsOpenPosMeasure] :
    Function.Injective (⇑(toLp p μ 𝕜 : (α ->ᵇ E) ->L[𝕜] Lp E p μ)) :=
  fun _f _g hfg => (toLp_inj μ).mp hfg

end BoundedContinuousFunction

namespace ContinuousMap

variable [CompactSpace α] [IsFiniteMeasure μ]
variable (𝕜 : Type*) (p μ) [Fact (1 <= p)]
  [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/--
Definition of `toLp` / `toLp` 的定义

English:
definition toLp
  signature: : C(α, E) ->L[𝕜] Lp E p μ
  body: (BoundedContinuousFunction.toLp p μ 𝕜).comp
    (linearIsometryBoundedOfCompact α E 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

中文:
定义 toLp
  签名: : C(α, E) ->L[𝕜] Lp E p μ
  定义体: (BoundedContinuousFunction.toLp p μ 𝕜).comp
    (linearIsometryBoundedOfCompact α E 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.toLp, linearIsometryBoundedOfCompact, toContinuousLinearEquiv, toContinuousLinearEquiv.toContinuousLinearMap, toContinuousLinearMap
-/
noncomputable def toLp : C(α, E) ->L[𝕜] Lp E p μ :=
  (BoundedContinuousFunction.toLp p μ 𝕜).comp
    (linearIsometryBoundedOfCompact α E 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

variable {𝕜}

/--
theorem `range_toLp` / 定理 `range_toLp`

English:
theorem range_toLp
  proof: by
  refine SetLike.ext' ?_
  have := (linearIsometryBoundedOfCompact α E 𝕜).surjective
  convert! Function.Surjective.range_comp this (BoundedContinuousFunction.toLp (E := E) p μ 𝕜)
  rw [← BoundedContinuousFunction.range_toLp p μ (𝕜 := 𝕜)]; rw [Submodule.coe_toAddSubgroup]; rw [LinearMap.coe_range

中文:
定理 range_toLp
  证明: by
  refine SetLike.ext' ?_
  have := (linearIsometryBoundedOfCompact α E 𝕜).surjective
  convert! Function.Surjective.range_comp this (BoundedContinuousFunction.toLp (E := E) p μ 𝕜)
  rw [← BoundedContinuousFunction.range_toLp p μ (𝕜 := 𝕜)]; rw [Submodule.coe_toAddSubgroup]; rw [LinearMap.coe_range

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.range_toLp, BoundedContinuousFunction.toLp, ContinuousLinearMap, ContinuousLinearMap.coe_coe, Function, Function.Surjective.range_comp, LinearMap, LinearMap.coe_range, SetLike, SetLike.ext, Submodule, Submodule.coe_toAddSubgroup, Surjective, coe_coe, coe_range, coe_toAddSubgroup, convert, linearIsometryBoundedOfCompact, range_comp
-/
theorem range_toLp :
    (toLp p μ 𝕜 : C(α, E) ->L[𝕜] Lp E p μ).range.toAddSubgroup =
      MeasureTheory.Lp.boundedContinuousFunction E p μ := by
  refine SetLike.ext' ?_
  have := (linearIsometryBoundedOfCompact α E 𝕜).surjective
  convert! Function.Surjective.range_comp this (BoundedContinuousFunction.toLp (E := E) p μ 𝕜)
  rw [← BoundedContinuousFunction.range_toLp p μ (𝕜 := 𝕜)]; rw [Submodule.coe_toAddSubgroup]; rw [LinearMap.coe_range]; rw [ContinuousLinearMap.coe_coe]

variable {p}

/--
theorem `coeFn_toLp` / 定理 `coeFn_toLp`

English:
theorem coeFn_toLp
  given: (f : C(α, E))
  proof: AEEqFun.coeFn_mk f _

中文:
定理 coeFn_toLp
  条件: (f : C(α, E))
  证明: AEEqFun.coeFn_mk f _
-/
theorem coeFn_toLp (f : C(α, E)) :
    toLp (E := E) p μ 𝕜 f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f _

/--
theorem `toLp_def` / 定理 `toLp_def`

English:
theorem toLp_def
  given: (f : C(α, E))
  proof: rfl

@[simp]

中文:
定理 toLp_def
  条件: (f : C(α, E))
  证明: rfl

@[simp]
-/
theorem toLp_def (f : C(α, E)) :
    toLp (E := E) p μ 𝕜 f =
      BoundedContinuousFunction.toLp (E := E) p μ 𝕜 (linearIsometryBoundedOfCompact α E 𝕜 f) :=
  rfl

@[simp]
/--
theorem `toLp_comp_toContinuousMap` / 定理 `toLp_comp_toContinuousMap`

English:
theorem toLp_comp_toContinuousMap
  given: (f : α ->ᵇ E)
  proof: rfl

@[simp]

中文:
定理 toLp_comp_toContinuousMap
  条件: (f : α ->ᵇ E)
  证明: rfl

@[simp]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.toLp, f.toContinuousMap, toContinuousMap
-/
theorem toLp_comp_toContinuousMap (f : α ->ᵇ E) :
    toLp (E := E) p μ 𝕜 f.toContinuousMap = BoundedContinuousFunction.toLp (E := E) p μ 𝕜 f :=
  rfl

@[simp]
/--
theorem `coe_toLp` / 定理 `coe_toLp`

English:
theorem coe_toLp
  given: (f : C(α, E))
  proof: rfl

中文:
定理 coe_toLp
  条件: (f : C(α, E))
  证明: rfl

Depends on / 依赖: f.toAEEqFun, toAEEqFun
-/
theorem coe_toLp (f : C(α, E)) :
    (toLp (E := E) p μ 𝕜 f : α ->ₘ[μ] E) = f.toAEEqFun μ :=
  rfl

/--
theorem `toLp_injective` / 定理 `toLp_injective`

English:
theorem toLp_injective
  given: [μ.IsOpenPosMeasure]
  proof: (BoundedContinuousFunction.toLp_injective _).comp (linearIsometryBoundedOfCompact α E 𝕜).injective

中文:
定理 toLp_injective
  条件: [μ.IsOpenPosMeasure]
  证明: (BoundedContinuousFunction.toLp_injective _).comp (linearIsometryBoundedOfCompact α E 𝕜).injective

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.toLp_injective, injective, linearIsometryBoundedOfCompact, toLp_injective
-/
theorem toLp_injective [μ.IsOpenPosMeasure] :
    Function.Injective (⇑(toLp p μ 𝕜 : C(α, E) ->L[𝕜] Lp E p μ)) :=
  (BoundedContinuousFunction.toLp_injective _).comp (linearIsometryBoundedOfCompact α E 𝕜).injective

/--
theorem `toLp_inj` / 定理 `toLp_inj`

English:
theorem toLp_inj
  given: {f g : C(α, E)} [μ.IsOpenPosMeasure]
  proof: (toLp_injective μ).eq_iff

中文:
定理 toLp_inj
  条件: {f g : C(α, E)} [μ.IsOpenPosMeasure]
  证明: (toLp_injective μ).eq_iff
-/
theorem toLp_inj {f g : C(α, E)} [μ.IsOpenPosMeasure] :
    toLp (E := E) p μ 𝕜 f = toLp (E := E) p μ 𝕜 g ↔ f = g :=
  (toLp_injective μ).eq_iff

variable {μ}

/--
theorem `hasSum_of_hasSum_Lp` / 定理 `hasSum_of_hasSum_Lp`

English:
theorem hasSum_of_hasSum_Lp
  statement: {β : Type*} [μ.IsOpenPosMeasure]
  proof: by
  convert! Summable.hasSum hg
  exact toLp_injective μ (hg2.unique ((toLp p μ 𝕜).hasSum <| Summable.hasSum hg))

中文:
定理 hasSum_of_hasSum_Lp
  结论: {β : 类型} [μ.IsOpenPosMeasure]
  证明: by
  convert! Summable.hasSum hg
  exact toLp_injective μ (hg2.unique ((toLp p μ 𝕜).hasSum <| Summable.hasSum hg))

Depends on / 依赖: HasSum, Summable, Summable.hasSum, convert, hasSum, hg2.unique, toLp_injective, unique
-/
theorem hasSum_of_hasSum_Lp {β : Type*} [μ.IsOpenPosMeasure]
    {g : β -> C(α, E)} {f : C(α, E)} (hg : Summable g)
    (hg2 : HasSum (toLp (E := E) p μ 𝕜 ∘ g) (toLp (E := E) p μ 𝕜 f)) : HasSum g f := by
  convert! Summable.hasSum hg
  exact toLp_injective μ (hg2.unique ((toLp p μ 𝕜).hasSum <| Summable.hasSum hg))

variable (μ) {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

/--
theorem `toLp_norm_eq_toLp_norm_coe` / 定理 `toLp_norm_eq_toLp_norm_coe`

English:
theorem toLp_norm_eq_toLp_norm_coe
  proof: ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _

中文:
定理 toLp_norm_eq_toLp_norm_coe
  证明: ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, opNorm_comp_linearIsometryEquiv
-/
theorem toLp_norm_eq_toLp_norm_coe :
    ‖(toLp p μ 𝕜 : C(α, E) ->L[𝕜] Lp E p μ)‖ =
      ‖(BoundedContinuousFunction.toLp p μ 𝕜 : (α ->ᵇ E) ->L[𝕜] Lp E p μ)‖ :=
  ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _

/--
theorem `toLp_norm_le` / 定理 `toLp_norm_le`

English:
theorem toLp_norm_le
  proof: by
  rw [toLp_norm_eq_toLp_norm_coe]
  exact BoundedContinuousFunction.toLp_norm_le μ

中文:
定理 toLp_norm_le
  证明: by
  rw [toLp_norm_eq_toLp_norm_coe]
  exact BoundedContinuousFunction.toLp_norm_le μ

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.toLp_norm_le, toLp_norm_eq_toLp_norm_coe, toLp_norm_le
-/
theorem toLp_norm_le :
    ‖(toLp p μ 𝕜 : C(α, E) ->L[𝕜] Lp E p μ)‖ <= measureUnivNNReal μ ^ p.toReal⁻¹ := by
  rw [toLp_norm_eq_toLp_norm_coe]
  exact BoundedContinuousFunction.toLp_norm_le μ

/--
lemma `memLp` / 引理 `memLp`

English:
lemma memLp
  given: (𝕜' : Type*) [NormedField 𝕜'] [NormedSpace 𝕜' E] (f : C(α, E))
  proof: by
  have := Lp.mem_Lp_iff_memLp.mp (Subtype.val_prop (f.toLp p μ 𝕜'))
  rwa [coe_toLp, memLp_congr_ae (coeFn_toAEEqFun _ _)] at this

中文:
引理 memLp
  条件: (𝕜' : 类型) [NormedField 𝕜'] [NormedSpace 𝕜' E] (f : C(α, E))
  证明: by
  have := Lp.mem_Lp_iff_memLp.mp (Subtype.val_prop (f.toLp p μ 𝕜'))
  rwa [coe_toLp, memLp_congr_ae (coeFn_toAEEqFun _ _)] at this

Depends on / 依赖: Lp.mem_Lp_iff_memLp.mp, Subtype, Subtype.val_prop, coeFn_toAEEqFun, coe_toLp, f.toLp, memLp_congr_ae, mem_Lp_iff_memLp, val_prop
-/
lemma memLp (𝕜' : Type*) [NormedField 𝕜'] [NormedSpace 𝕜' E] (f : C(α, E)) :
    MemLp f p μ := by
  have := Lp.mem_Lp_iff_memLp.mp (Subtype.val_prop (f.toLp p μ 𝕜'))
  rwa [coe_toLp, memLp_congr_ae (coeFn_toAEEqFun _ _)] at this

end ContinuousMap
