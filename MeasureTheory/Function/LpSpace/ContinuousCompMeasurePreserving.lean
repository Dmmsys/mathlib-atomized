/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Measure.ContinuousPreimage

/-!
# Continuity of `MeasureTheory.Lp.compMeasurePreserving`

In this file we prove that the composition of an `L^p` function `g`
with a continuous measure-preserving map `f` is continuous in both arguments.

First, we prove it for indicator functions,
in terms of convergence of `μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))` to zero.

Then we prove the continuity of the function of two arguments
defined on `MeasureTheory.Lp E p ν × {f : C(X, Y) // MeasurePreserving f μ ν}`.

Finally, we provide dot notation convenience lemmas.
-/

public section

open Filter Set MeasureTheory
open scoped ENNReal Topology symmDiff

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
  {μ : Measure X} {ν : Measure Y} [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]

namespace MeasureTheory
namespace Lp

variable (μ ν)
variable (E : Type*) [NormedAddCommGroup E] {p : Real>=0∞} [Fact (1 <= p)]

/--
theorem `compMeasurePreserving_continuous` / 定理 `compMeasurePreserving_continuous`

English:
theorem compMeasurePreserving_continuous
  given: (hp : p != ∞)
  proof: by
  have hp₀ : p != 0 := (one_pos.trans_le Fact.out).ne'
  refine continuous_prod_of_dense_continuous_lipschitzWith _ 1
    (MeasureTheory.Lp.simpleFunc.dense hp) ?_ fun f => (isometry_compMeasurePreserving f.2).lipschitz
  intro f hf
  lift f to Lp.simpleFunc E p ν using hf
  induction f using Lp.simpleFunc.induction hp₀ hp with
  | add hfp hgp _ ihf ihg => exact ihf.add ihg
  | @indicatorConst c s hs hνs =>
    dsimp only [Lp.simpleFunc.coe_indicatorConst, Lp.indicatorConstLp_compMeasurePreserving]
    refine continuous_indicatorConstLp_set hp fun f => ?_
    apply tendsto_measure_symmDiff_preimage_nhds_zero continuousAt_subtype_val _ f.2
      hs.nullMeasurableSet hνs.ne
    exact .of_forall Subtype.property

中文:
定理 compMeasurePreserving_continuous
  条件: (hp : p != ∞)
  证明: by
  have hp₀ : p != 0 := (one_pos.trans_le Fact.out).ne'
  refine continuous_prod_of_dense_continuous_lipschitzWith _ 1
    (MeasureTheory.Lp.simpleFunc.dense hp) ?_ fun f => (isometry_compMeasurePreserving f.2).lipschitz
  intro f hf
  lift f to Lp.simpleFunc E p ν using hf
  induction f using Lp.simpleFunc.induction hp₀ hp with
  | add hfp hgp _ ihf ihg => exact ihf.add ihg
  | @indicatorConst c s hs hνs =>
    dsimp only [Lp.simpleFunc.coe_indicatorConst, Lp.indicatorConstLp_compMeasurePreserving]
    refine continuous_indicatorConstLp_set hp fun f => ?_
    apply tendsto_measure_symmDiff_preimage_nhds_zero continuousAt_subtype_val _ f.2
      hs.nullMeasurableSet hνs.ne
    exact .of_forall Subtype.property

Depends on / 依赖: Fact.out, Lp.indicatorConstLp_compMeasurePreserving, Lp.simpleFunc, Lp.simpleFunc.coe_indicatorConst, Lp.simpleFunc.induction, MeasureTheory, MeasureTheory.Lp.simpleFunc.dense, coe_indicatorConst, continuo, continuous_prod_of_dense_continuous_lipschitzWith, ihf.add, indicatorConst, indicatorConstLp_compMeasurePreserving, isometry_compMeasurePreserving, lipschitz, one_pos, one_pos.trans_le, simpleFunc, trans_le
-/
theorem compMeasurePreserving_continuous (hp : p != ∞) :
    Continuous fun gf : Lp E p ν × {f : C(X, Y) // MeasurePreserving f μ ν} =>
      compMeasurePreserving gf.2.1 gf.2.2 gf.1 := by
  have hp₀ : p != 0 := (one_pos.trans_le Fact.out).ne'
  refine continuous_prod_of_dense_continuous_lipschitzWith _ 1
    (MeasureTheory.Lp.simpleFunc.dense hp) ?_ fun f => (isometry_compMeasurePreserving f.2).lipschitz
  intro f hf
  lift f to Lp.simpleFunc E p ν using hf
  induction f using Lp.simpleFunc.induction hp₀ hp with
  | add hfp hgp _ ihf ihg => exact ihf.add ihg
  | @indicatorConst c s hs hνs =>
    dsimp only [Lp.simpleFunc.coe_indicatorConst, Lp.indicatorConstLp_compMeasurePreserving]
    refine continuous_indicatorConstLp_set hp fun f => ?_
    apply tendsto_measure_symmDiff_preimage_nhds_zero continuousAt_subtype_val _ f.2
      hs.nullMeasurableSet hνs.ne
    exact .of_forall Subtype.property

end Lp

end MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] {p : Real>=0∞} [Fact (1 <= p)]

/--
theorem `Filter.Tendsto.compMeasurePreservingLp` / 定理 `Filter.Tendsto.compMeasurePreservingLp`

English:
theorem Filter.Tendsto.compMeasurePreservingLp
  statement: {α : Type*} {l : Filter α}
  proof: by
  have := (Lp.compMeasurePreserving_continuous μ ν E hp).tendsto ⟨f₀, g₀, hgm₀⟩
  replace hg : Tendsto (fun a => ⟨g a, hgm a⟩ : α -> {g : C(X, Y) // MeasurePreserving g μ ν})
      l (𝓝 ⟨g₀, hgm₀⟩) :=
    tendsto_subtype_rng.2 hg
  convert! this.comp (hf.prodMk_nhds hg)

中文:
定理 滤子.收敛.compMeasurePreservingLp
  结论: {α : 类型} {l : 滤子 α}
  证明: by
  have := (Lp.compMeasurePreserving_continuous μ ν E hp).tendsto ⟨f₀, g₀, hgm₀⟩
  replace hg : Tendsto (fun a => ⟨g a, hgm a⟩ : α -> {g : C(X, Y) // MeasurePreserving g μ ν})
      l (𝓝 ⟨g₀, hgm₀⟩) :=
    tendsto_subtype_rng.2 hg
  convert! this.comp (hf.prodMk_nhds hg)

Depends on / 依赖: Lp.compMeasurePreserving_continuous, MeasurePreserving, Tendsto, compMeasurePreserving_continuous, convert, hf.prodMk_nhds, prodMk_nhds, replace, tendsto, tendsto_subtype_rng, this.comp
-/
theorem Filter.Tendsto.compMeasurePreservingLp {α : Type*} {l : Filter α}
    {f : α -> Lp E p ν} {f₀ : Lp E p ν} {g : α -> C(X, Y)} {g₀ : C(X, Y)}
    (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 g₀))
    (hgm : forall a, MeasurePreserving (g a) μ ν) (hgm₀ : MeasurePreserving g₀ μ ν) (hp : p != ∞) :
    Tendsto (fun a => Lp.compMeasurePreserving (g a) (hgm a) (f a)) l
      (𝓝 (Lp.compMeasurePreserving g₀ hgm₀ f₀)) := by
  have := (Lp.compMeasurePreserving_continuous μ ν E hp).tendsto ⟨f₀, g₀, hgm₀⟩
  replace hg : Tendsto (fun a => ⟨g a, hgm a⟩ : α -> {g : C(X, Y) // MeasurePreserving g μ ν})
      l (𝓝 ⟨g₀, hgm₀⟩) :=
    tendsto_subtype_rng.2 hg
  convert! this.comp (hf.prodMk_nhds hg)

variable {Z : Type*} [TopologicalSpace Z] {f : Z -> Lp E p ν} {g : Z -> C(X, Y)} {s : Set Z} {z : Z}

/--
theorem `ContinuousWithinAt.compMeasurePreservingLp` / 定理 `ContinuousWithinAt.compMeasurePreservingLp`

English:
theorem ContinuousWithinAt.compMeasurePreservingLp
  statement: (hf : ContinuousWithinAt f s z)
  proof: Tendsto.compMeasurePreservingLp hf hg _ _ hp

中文:
定理 ContinuousWithinAt.compMeasurePreservingLp
  结论: (hf : ContinuousWithinAt f s z)
  证明: Tendsto.compMeasurePreservingLp hf hg _ _ hp

Depends on / 依赖: Tendsto, Tendsto.compMeasurePreservingLp, compMeasurePreservingLp
-/
theorem ContinuousWithinAt.compMeasurePreservingLp (hf : ContinuousWithinAt f s z)
    (hg : ContinuousWithinAt g s z) (hgm : forall z, MeasurePreserving (g z) μ ν) (hp : p != ∞) :
    ContinuousWithinAt (fun z => Lp.compMeasurePreserving (g z) (hgm z) (f z)) s z :=
  Tendsto.compMeasurePreservingLp hf hg _ _ hp

/--
theorem `ContinuousAt.compMeasurePreservingLp` / 定理 `ContinuousAt.compMeasurePreservingLp`

English:
theorem ContinuousAt.compMeasurePreservingLp
  statement: (hf : ContinuousAt f z)
  proof: Tendsto.compMeasurePreservingLp hf hg _ _ hp

中文:
定理 ContinuousAt.compMeasurePreservingLp
  结论: (hf : ContinuousAt f z)
  证明: Tendsto.compMeasurePreservingLp hf hg _ _ hp

Depends on / 依赖: Tendsto, Tendsto.compMeasurePreservingLp, compMeasurePreservingLp
-/
theorem ContinuousAt.compMeasurePreservingLp (hf : ContinuousAt f z)
    (hg : ContinuousAt g z) (hgm : forall z, MeasurePreserving (g z) μ ν) (hp : p != ∞) :
    ContinuousAt (fun z => Lp.compMeasurePreserving (g z) (hgm z) (f z)) z :=
  Tendsto.compMeasurePreservingLp hf hg _ _ hp

/--
theorem `ContinuousOn.compMeasurePreservingLp` / 定理 `ContinuousOn.compMeasurePreservingLp`

English:
theorem ContinuousOn.compMeasurePreservingLp
  statement: (hf : ContinuousOn f s)
  proof: fun z hz =>
  (hf z hz).compMeasurePreservingLp (hg z hz) hgm hp

中文:
定理 ContinuousOn.compMeasurePreservingLp
  结论: (hf : ContinuousOn f s)
  证明: fun z hz =>
  (hf z hz).compMeasurePreservingLp (hg z hz) hgm hp
-/
theorem ContinuousOn.compMeasurePreservingLp (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) (hgm : forall z, MeasurePreserving (g z) μ ν) (hp : p != ∞) :
    ContinuousOn (fun z => Lp.compMeasurePreserving (g z) (hgm z) (f z)) s := fun z hz =>
  (hf z hz).compMeasurePreservingLp (hg z hz) hgm hp

/--
theorem `Continuous.compMeasurePreservingLp` / 定理 `Continuous.compMeasurePreservingLp`

English:
theorem Continuous.compMeasurePreservingLp
  statement: (hf : Continuous f) (hg : Continuous g)
  proof: continuous_iff_continuousAt.mpr fun _ =>
    hf.continuousAt.compMeasurePreservingLp hg.continuousAt hgm hp

中文:
定理 连续.compMeasurePreservingLp
  结论: (hf : 连续 f) (hg : 连续 g)
  证明: continuous_iff_continuousAt.mpr fun _ =>
    hf.continuousAt.compMeasurePreservingLp hg.continuousAt hgm hp

Depends on / 依赖: compMeasurePreservingLp, continuousAt, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, hf.continuousAt.compMeasurePreservingLp, hg.continuousAt
-/
theorem Continuous.compMeasurePreservingLp (hf : Continuous f) (hg : Continuous g)
    (hgm : forall z, MeasurePreserving (g z) μ ν) (hp : p != ∞) :
    Continuous (fun z => Lp.compMeasurePreserving (g z) (hgm z) (f z)) :=
  continuous_iff_continuousAt.mpr fun _ =>
    hf.continuousAt.compMeasurePreservingLp hg.continuousAt hgm hp
