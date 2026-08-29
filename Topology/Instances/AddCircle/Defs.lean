/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Algebra.Ring.AddAut
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Divisible
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.GroupTheory.QuotientGroup.ModEq

/-!
# The additive circle

We define the additive circle `AddCircle p` as the quotient `𝕜 ⧸ ℤ ∙ p` for some period `p : 𝕜`.

See also `Circle` and `Real.Angle`. For the normed group structure on `AddCircle`, see
`AddCircle.NormedAddCommGroup` in a later file.

## Main definitions and results:

* `AddCircle`: the additive circle `𝕜 ⧸ ℤ ∙ p` for some period `p : 𝕜`
* `UnitAddCircle`: the special case `ℝ ⧸ ℤ`
* `AddCircle.equivAddCircle`: the rescaling equivalence `AddCircle p ≃+ AddCircle q`
* `AddCircle.equivIco` and `AddCircle.equivIoc`: the natural equivalences
  `AddCircle p ≃ Ico a (a + p)` and `AddCircle p ≃ Ioc a (a + p)`
* `AddCircle.addOrderOf_div_of_gcd_eq_one`: rational points have finite order
* `AddCircle.exists_gcd_eq_one_of_isOfFinAddOrder`: finite-order points are rational
* `AddCircle.homeoIccQuot`: the natural topological equivalence between `AddCircle p` and
  `Icc a (a + p)` with its endpoints identified.
* `AddCircle.liftIco_continuous` and `AddCircle.liftIoc_continuous`: if `f : ℝ → B` is continuous,
  and `f a = f (a + p)` for some `a`, then there is a continuous function `AddCircle p → B`
  which agrees with `f` on `Icc a (a + p)`.

## Implementation notes:

Although the most important case is `𝕜 = ℝ` we wish to support other types of scalars, such as
the rational circle `AddCircle (1 : ℚ)`, and so we set things up more generally.

## TODO

* Link with periodicity
* Lie group structure
* Exponential equivalence to `Circle`

-/

@[expose] public section


noncomputable section

open AddCommGroup Set Function AddSubgroup TopologicalSpace

open Topology

variable {𝕜 B : Type*}

section Continuity

variable [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] [Archimedean 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {p : 𝕜} (hp : 0 < p) (a x : 𝕜)

/--
theorem `eventuallyEq_toIcoDiv_nhdsGE` / 定理 `eventuallyEq_toIcoDiv_nhdsGE`

English:
theorem eventuallyEq_toIcoDiv_nhdsGE
  statement: toIcoDiv hp a =ᶠ[𝓝[>=] x] fun _ => toIcoDiv hp a x
  proof: by
  simp only [Filter.EventuallyEq, toIcoDiv_eq_iff, sub_mem_Ico_iff_left]
  apply Ico_mem_nhdsGE_of_mem
  rw [← sub_mem_Ico_iff_left]; rw [← toIcoDiv_eq_iff]

中文:
定理 eventuallyEq_toIcoDiv_nhdsGE
  结论: toIcoDiv hp a =ᶠ[𝓝[>=] x] fun _ => toIcoDiv hp a x
  证明: by
  simp only [Filter.EventuallyEq, toIcoDiv_eq_iff, sub_mem_Ico_iff_left]
  apply Ico_mem_nhdsGE_of_mem
  rw [← sub_mem_Ico_iff_left]; rw [← toIcoDiv_eq_iff]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Ico_mem_nhdsGE_of_mem, sub_mem_Ico_iff_left, toIcoDiv_eq_iff
-/
theorem eventuallyEq_toIcoDiv_nhdsGE : toIcoDiv hp a =ᶠ[𝓝[>=] x] fun _ => toIcoDiv hp a x := by
  simp only [Filter.EventuallyEq, toIcoDiv_eq_iff, sub_mem_Ico_iff_left]
  apply Ico_mem_nhdsGE_of_mem
  rw [← sub_mem_Ico_iff_left]; rw [← toIcoDiv_eq_iff]

/--
theorem `continuousWithinAt_toIcoDiv_Ici` / 定理 `continuousWithinAt_toIcoDiv_Ici`

English:
theorem continuousWithinAt_toIcoDiv_Ici
  statement: ContinuousWithinAt (toIcoDiv hp a) (Ici x) x
  proof: .mono_right pure_le_nhds _ Filter.tendsto_pure.mpr (eventuallyEq_toIcoDiv_nhdsGE hp a x)

中文:
定理 continuousWithinAt_toIcoDiv_Ici
  结论: ContinuousWithinAt (toIcoDiv hp a) (左闭右无界区间 x) x
  证明: .mono_right pure_le_nhds _ Filter.tendsto_pure.mpr (eventuallyEq_toIcoDiv_nhdsGE hp a x)

Depends on / 依赖: Filter, Filter.tendsto_pure.mpr, eventuallyEq_toIcoDiv_nhdsGE, mono_right, pure_le_nhds, tendsto_pure
-/
theorem continuousWithinAt_toIcoDiv_Ici : ContinuousWithinAt (toIcoDiv hp a) (Ici x) x :=
.mono_right pure_le_nhds _ Filter.tendsto_pure.mpr (eventuallyEq_toIcoDiv_nhdsGE hp a x)

/--
theorem `eventuallyEq_toIocDiv_nhdsLE` / 定理 `eventuallyEq_toIocDiv_nhdsLE`

English:
theorem eventuallyEq_toIocDiv_nhdsLE
  statement: toIocDiv hp a =ᶠ[𝓝[<=] x] fun _ => toIocDiv hp a x
  proof: by
  simp only [Filter.EventuallyEq, toIocDiv_eq_iff, sub_mem_Ioc_iff_left]
  apply Ioc_mem_nhdsLE_of_mem
  rw [← sub_mem_Ioc_iff_left]; rw [← toIocDiv_eq_iff]

中文:
定理 eventuallyEq_toIocDiv_nhdsLE
  结论: toIocDiv hp a =ᶠ[𝓝[<=] x] fun _ => toIocDiv hp a x
  证明: by
  simp only [Filter.EventuallyEq, toIocDiv_eq_iff, sub_mem_Ioc_iff_left]
  apply Ioc_mem_nhdsLE_of_mem
  rw [← sub_mem_Ioc_iff_left]; rw [← toIocDiv_eq_iff]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Ioc_mem_nhdsLE_of_mem, sub_mem_Ioc_iff_left, toIocDiv_eq_iff
-/
theorem eventuallyEq_toIocDiv_nhdsLE : toIocDiv hp a =ᶠ[𝓝[<=] x] fun _ => toIocDiv hp a x := by
  simp only [Filter.EventuallyEq, toIocDiv_eq_iff, sub_mem_Ioc_iff_left]
  apply Ioc_mem_nhdsLE_of_mem
  rw [← sub_mem_Ioc_iff_left]; rw [← toIocDiv_eq_iff]

/--
theorem `continuousWithinAt_toIocDiv_Iic` / 定理 `continuousWithinAt_toIocDiv_Iic`

English:
theorem continuousWithinAt_toIocDiv_Iic
  statement: ContinuousWithinAt (toIocDiv hp a) (Iic x) x
  proof: .mono_right pure_le_nhds _ Filter.tendsto_pure.mpr (eventuallyEq_toIocDiv_nhdsLE hp a x)

中文:
定理 continuousWithinAt_toIocDiv_Iic
  结论: ContinuousWithinAt (toIocDiv hp a) (左无界右闭区间 x) x
  证明: .mono_right pure_le_nhds _ Filter.tendsto_pure.mpr (eventuallyEq_toIocDiv_nhdsLE hp a x)

Depends on / 依赖: Filter, Filter.tendsto_pure.mpr, eventuallyEq_toIocDiv_nhdsLE, mono_right, pure_le_nhds, tendsto_pure
-/
theorem continuousWithinAt_toIocDiv_Iic : ContinuousWithinAt (toIocDiv hp a) (Iic x) x :=
.mono_right pure_le_nhds _ Filter.tendsto_pure.mpr (eventuallyEq_toIocDiv_nhdsLE hp a x)

/--
theorem `continuousWithinAt_toIcoMod_Ici` / 定理 `continuousWithinAt_toIcoMod_Ici`

English:
theorem continuousWithinAt_toIcoMod_Ici
  statement: ContinuousWithinAt (toIcoMod hp a) (Ici x) x
  proof: continuousWithinAt_id.sub
    (continuousWithinAt_toIcoDiv_Ici hp a x).smul continuousWithinAt_const

@[deprecated (since := "2026-01-04")]
alias continuous_right_toIcoMod := continuousWithinAt_toIcoMod_Ici

中文:
定理 continuousWithinAt_toIcoMod_Ici
  结论: ContinuousWithinAt (toIcoMod hp a) (左闭右无界区间 x) x
  证明: continuousWithinAt_id.sub
    (continuousWithinAt_toIcoDiv_Ici hp a x).smul continuousWithinAt_const

@[deprecated (since := "2026-01-04")]
alias continuous_right_toIcoMod := continuousWithinAt_toIcoMod_Ici

Depends on / 依赖: continuousWithinAt_const, continuousWithinAt_id, continuousWithinAt_id.sub, continuousWithinAt_toIcoDiv_Ici
-/
theorem continuousWithinAt_toIcoMod_Ici : ContinuousWithinAt (toIcoMod hp a) (Ici x) x :=
continuousWithinAt_id.sub
    (continuousWithinAt_toIcoDiv_Ici hp a x).smul continuousWithinAt_const

@[deprecated (since := "2026-01-04")]
alias continuous_right_toIcoMod := continuousWithinAt_toIcoMod_Ici

/--
theorem `continuousWithinAt_toIocMod_Iic` / 定理 `continuousWithinAt_toIocMod_Iic`

English:
theorem continuousWithinAt_toIocMod_Iic
  statement: ContinuousWithinAt (toIocMod hp a) (Iic x) x
  proof: continuousWithinAt_id.sub
    (continuousWithinAt_toIocDiv_Iic hp a x).smul continuousWithinAt_const

@[deprecated (since := "2026-01-04")]
alias continuous_left_toIocMod := continuousWithinAt_toIocMod_Iic

中文:
定理 continuousWithinAt_toIocMod_Iic
  结论: ContinuousWithinAt (toIocMod hp a) (左无界右闭区间 x) x
  证明: continuousWithinAt_id.sub
    (continuousWithinAt_toIocDiv_Iic hp a x).smul continuousWithinAt_const

@[deprecated (since := "2026-01-04")]
alias continuous_left_toIocMod := continuousWithinAt_toIocMod_Iic

Depends on / 依赖: continuousWithinAt_const, continuousWithinAt_id, continuousWithinAt_id.sub, continuousWithinAt_toIocDiv_Iic
-/
theorem continuousWithinAt_toIocMod_Iic : ContinuousWithinAt (toIocMod hp a) (Iic x) x :=
continuousWithinAt_id.sub
    (continuousWithinAt_toIocDiv_Iic hp a x).smul continuousWithinAt_const

@[deprecated (since := "2026-01-04")]
alias continuous_left_toIocMod := continuousWithinAt_toIocMod_Iic

/--
theorem `eventuallyEq_toIcoDiv_nhdsLT` / 定理 `eventuallyEq_toIcoDiv_nhdsLT`

English:
theorem eventuallyEq_toIcoDiv_nhdsLT
  statement: toIcoDiv hp a =ᶠ[𝓝[<] x] fun _ => toIocDiv hp a x
  proof: by
  simp only [Filter.EventuallyEq, toIcoDiv_eq_iff, sub_mem_Ico_iff_left]
  apply Ico_mem_nhdsLT_of_mem
  rw [← sub_mem_Ioc_iff_left]; rw [← toIocDiv_eq_iff]

中文:
定理 eventuallyEq_toIcoDiv_nhdsLT
  结论: toIcoDiv hp a =ᶠ[𝓝[<] x] fun _ => toIocDiv hp a x
  证明: by
  simp only [Filter.EventuallyEq, toIcoDiv_eq_iff, sub_mem_Ico_iff_left]
  apply Ico_mem_nhdsLT_of_mem
  rw [← sub_mem_Ioc_iff_left]; rw [← toIocDiv_eq_iff]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Ico_mem_nhdsLT_of_mem, sub_mem_Ico_iff_left, sub_mem_Ioc_iff_left, toIcoDiv_eq_iff, toIocDiv_eq_iff
-/
theorem eventuallyEq_toIcoDiv_nhdsLT : toIcoDiv hp a =ᶠ[𝓝[<] x] fun _ => toIocDiv hp a x := by
  simp only [Filter.EventuallyEq, toIcoDiv_eq_iff, sub_mem_Ico_iff_left]
  apply Ico_mem_nhdsLT_of_mem
  rw [← sub_mem_Ioc_iff_left]; rw [← toIocDiv_eq_iff]

/--
theorem `eventuallyEq_toIocDiv_nhdsGT` / 定理 `eventuallyEq_toIocDiv_nhdsGT`

English:
theorem eventuallyEq_toIocDiv_nhdsGT
  statement: toIocDiv hp a =ᶠ[𝓝[>] x] fun _ => toIcoDiv hp a x
  proof: by
  simp only [Filter.EventuallyEq, toIocDiv_eq_iff, sub_mem_Ioc_iff_left]
  apply Ioc_mem_nhdsGT_of_mem
  rw [← sub_mem_Ico_iff_left]; rw [← toIcoDiv_eq_iff]

中文:
定理 eventuallyEq_toIocDiv_nhdsGT
  结论: toIocDiv hp a =ᶠ[𝓝[>] x] fun _ => toIcoDiv hp a x
  证明: by
  simp only [Filter.EventuallyEq, toIocDiv_eq_iff, sub_mem_Ioc_iff_left]
  apply Ioc_mem_nhdsGT_of_mem
  rw [← sub_mem_Ico_iff_left]; rw [← toIcoDiv_eq_iff]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Ioc_mem_nhdsGT_of_mem, sub_mem_Ico_iff_left, sub_mem_Ioc_iff_left, toIcoDiv_eq_iff, toIocDiv_eq_iff
-/
theorem eventuallyEq_toIocDiv_nhdsGT : toIocDiv hp a =ᶠ[𝓝[>] x] fun _ => toIcoDiv hp a x := by
  simp only [Filter.EventuallyEq, toIocDiv_eq_iff, sub_mem_Ioc_iff_left]
  apply Ioc_mem_nhdsGT_of_mem
  rw [← sub_mem_Ico_iff_left]; rw [← toIcoDiv_eq_iff]

variable {x}

/--
theorem `eventuallyEq_toIcoDiv_nhds` / 定理 `eventuallyEq_toIcoDiv_nhds`

English:
theorem eventuallyEq_toIcoDiv_nhds
  given: (hx : ¬x ≡ a [PMOD p])
  proof: by
  rw [← nhdsLT_sup_nhdsGE]; rw [Filter.EventuallyEq]; rw [Filter.eventually_sup]
  refine ⟨?_, eventuallyEq_toIcoDiv_nhdsGE hp a x⟩
  convert! (eventuallyEq_toIcoDiv_nhdsLT hp a x).eventually using 3
  rwa [← not_modEq_iff_toIcoDiv_eq_toIocDiv, AddCommGroup.modEq_comm]

中文:
定理 eventuallyEq_toIcoDiv_nhds
  条件: (hx : ¬x ≡ a [PMOD p])
  证明: by
  rw [← nhdsLT_sup_nhdsGE]; rw [Filter.EventuallyEq]; rw [Filter.eventually_sup]
  refine ⟨?_, eventuallyEq_toIcoDiv_nhdsGE hp a x⟩
  convert! (eventuallyEq_toIcoDiv_nhdsLT hp a x).eventually using 3
  rwa [← not_modEq_iff_toIcoDiv_eq_toIocDiv, AddCommGroup.modEq_comm]

Depends on / 依赖: AddCommGroup, AddCommGroup.modEq_comm, EventuallyEq, Filter, Filter.EventuallyEq, Filter.eventually_sup, convert, eventually, eventuallyEq_toIcoDiv_nhdsGE, eventuallyEq_toIcoDiv_nhdsLT, eventually_sup, modEq_comm, nhdsLT_sup_nhdsGE, not_modEq_iff_toIcoDiv_eq_toIocDiv
-/
theorem eventuallyEq_toIcoDiv_nhds (hx : ¬x ≡ a [PMOD p]) :
    toIcoDiv hp a =ᶠ[𝓝 x] fun _ => toIcoDiv hp a x := by
  rw [← nhdsLT_sup_nhdsGE]; rw [Filter.EventuallyEq]; rw [Filter.eventually_sup]
  refine ⟨?_, eventuallyEq_toIcoDiv_nhdsGE hp a x⟩
  convert! (eventuallyEq_toIcoDiv_nhdsLT hp a x).eventually using 3
  rwa [← not_modEq_iff_toIcoDiv_eq_toIocDiv, AddCommGroup.modEq_comm]

/--
theorem `continuousAt_toIcoDiv` / 定理 `continuousAt_toIcoDiv`

English:
theorem continuousAt_toIcoDiv
  given: (hx : ¬x ≡ a [PMOD p])
  proof: tendsto_nhds_of_eventually_eq eventuallyEq_toIcoDiv_nhds hp a hx

中文:
定理 continuousAt_toIcoDiv
  条件: (hx : ¬x ≡ a [PMOD p])
  证明: tendsto_nhds_of_eventually_eq eventuallyEq_toIcoDiv_nhds hp a hx

Depends on / 依赖: eventuallyEq_toIcoDiv_nhds, tendsto_nhds_of_eventually_eq
-/
theorem continuousAt_toIcoDiv (hx : ¬x ≡ a [PMOD p]) :
    ContinuousAt (toIcoDiv hp a) x :=
tendsto_nhds_of_eventually_eq eventuallyEq_toIcoDiv_nhds hp a hx

/--
theorem `continuousOn_toIcoDiv` / 定理 `continuousOn_toIcoDiv`

English:
theorem continuousOn_toIcoDiv
  statement: ContinuousOn (toIcoDiv hp a) {x | ¬x ≡ a [PMOD p]}
  proof: fun _x hx =>
  (continuousAt_toIcoDiv hp a hx).continuousWithinAt

中文:
定理 continuousOn_toIcoDiv
  结论: ContinuousOn (toIcoDiv hp a) {x | ¬x ≡ a [PMOD p]}
  证明: fun _x hx =>
  (continuousAt_toIcoDiv hp a hx).continuousWithinAt
-/
theorem continuousOn_toIcoDiv : ContinuousOn (toIcoDiv hp a) {x | ¬x ≡ a [PMOD p]} := fun _x hx =>
  (continuousAt_toIcoDiv hp a hx).continuousWithinAt

/--
theorem `eventuallyEq_toIocDiv_nhds` / 定理 `eventuallyEq_toIocDiv_nhds`

English:
theorem eventuallyEq_toIocDiv_nhds
  given: (hx : ¬x ≡ a [PMOD p])
  proof: by
  rw [← nhdsLE_sup_nhdsGT]; rw [Filter.EventuallyEq]; rw [Filter.eventually_sup]
  refine ⟨eventuallyEq_toIocDiv_nhdsLE hp a x, ?_⟩
  convert! (eventuallyEq_toIocDiv_nhdsGT hp a x).eventually using 3
  rwa [eq_comm, ← not_modEq_iff_toIcoDiv_eq_toIocDiv, AddCommGroup.modEq_comm]

中文:
定理 eventuallyEq_toIocDiv_nhds
  条件: (hx : ¬x ≡ a [PMOD p])
  证明: by
  rw [← nhdsLE_sup_nhdsGT]; rw [Filter.EventuallyEq]; rw [Filter.eventually_sup]
  refine ⟨eventuallyEq_toIocDiv_nhdsLE hp a x, ?_⟩
  convert! (eventuallyEq_toIocDiv_nhdsGT hp a x).eventually using 3
  rwa [eq_comm, ← not_modEq_iff_toIcoDiv_eq_toIocDiv, AddCommGroup.modEq_comm]

Depends on / 依赖: AddCommGroup, AddCommGroup.modEq_comm, EventuallyEq, Filter, Filter.EventuallyEq, Filter.eventually_sup, convert, eq_comm, eventually, eventuallyEq_toIocDiv_nhdsGT, eventuallyEq_toIocDiv_nhdsLE, eventually_sup, modEq_comm, nhdsLE_sup_nhdsGT, not_modEq_iff_toIcoDiv_eq_toIocDiv
-/
theorem eventuallyEq_toIocDiv_nhds (hx : ¬x ≡ a [PMOD p]) :
    toIocDiv hp a =ᶠ[𝓝 x] fun _ => toIocDiv hp a x := by
  rw [← nhdsLE_sup_nhdsGT]; rw [Filter.EventuallyEq]; rw [Filter.eventually_sup]
  refine ⟨eventuallyEq_toIocDiv_nhdsLE hp a x, ?_⟩
  convert! (eventuallyEq_toIocDiv_nhdsGT hp a x).eventually using 3
  rwa [eq_comm, ← not_modEq_iff_toIcoDiv_eq_toIocDiv, AddCommGroup.modEq_comm]

/--
theorem `continuousAt_toIocDiv` / 定理 `continuousAt_toIocDiv`

English:
theorem continuousAt_toIocDiv
  given: (hx : ¬x ≡ a [PMOD p])
  proof: tendsto_nhds_of_eventually_eq eventuallyEq_toIocDiv_nhds hp a hx

中文:
定理 continuousAt_toIocDiv
  条件: (hx : ¬x ≡ a [PMOD p])
  证明: tendsto_nhds_of_eventually_eq eventuallyEq_toIocDiv_nhds hp a hx

Depends on / 依赖: eventuallyEq_toIocDiv_nhds, tendsto_nhds_of_eventually_eq
-/
theorem continuousAt_toIocDiv (hx : ¬x ≡ a [PMOD p]) :
    ContinuousAt (toIocDiv hp a) x :=
tendsto_nhds_of_eventually_eq eventuallyEq_toIocDiv_nhds hp a hx

/--
theorem `continuousOn_toIocDiv` / 定理 `continuousOn_toIocDiv`

English:
theorem continuousOn_toIocDiv
  proof: fun _x hx =>
  (continuousAt_toIocDiv hp a hx).continuousWithinAt

中文:
定理 continuousOn_toIocDiv
  证明: fun _x hx =>
  (continuousAt_toIocDiv hp a hx).continuousWithinAt
-/
theorem continuousOn_toIocDiv :
    ContinuousOn (toIocDiv hp a) {x | ¬x ≡ a [PMOD p]} := fun _x hx =>
  (continuousAt_toIocDiv hp a hx).continuousWithinAt

/--
theorem `toIcoMod_eventuallyEq_toIocMod` / 定理 `toIcoMod_eventuallyEq_toIocMod`

English:
theorem toIcoMod_eventuallyEq_toIocMod
  given: (hx : ¬x ≡ a [PMOD p])
  proof: by
  refine IsOpen.mem_nhds ?_ ?_
  · rw [Ico_eq_locus_Ioc_eq_iUnion_Ioo]
    exact isOpen_iUnion fun i => isOpen_Ioo
  · rwa [mem_ofPred_eq, ← not_modEq_iff_toIcoMod_eq_toIocMod hp, AddCommGroup.modEq_comm]

中文:
定理 toIcoMod_eventuallyEq_toIocMod
  条件: (hx : ¬x ≡ a [PMOD p])
  证明: by
  refine IsOpen.mem_nhds ?_ ?_
  · rw [Ico_eq_locus_Ioc_eq_iUnion_Ioo]
    exact isOpen_iUnion fun i => isOpen_Ioo
  · rwa [mem_ofPred_eq, ← not_modEq_iff_toIcoMod_eq_toIocMod hp, AddCommGroup.modEq_comm]

Depends on / 依赖: AddCommGroup, AddCommGroup.modEq_comm, Ico_eq_locus_Ioc_eq_iUnion_Ioo, IsOpen, IsOpen.mem_nhds, isOpen_Ioo, isOpen_iUnion, mem_nhds, mem_ofPred_eq, modEq_comm, not_modEq_iff_toIcoMod_eq_toIocMod
-/
theorem toIcoMod_eventuallyEq_toIocMod (hx : ¬x ≡ a [PMOD p]) :
    toIcoMod hp a =ᶠ[𝓝 x] toIocMod hp a := by
  refine IsOpen.mem_nhds ?_ ?_
  · rw [Ico_eq_locus_Ioc_eq_iUnion_Ioo]
    exact isOpen_iUnion fun i => isOpen_Ioo
  · rwa [mem_ofPred_eq, ← not_modEq_iff_toIcoMod_eq_toIocMod hp, AddCommGroup.modEq_comm]

/--
theorem `continuousAt_toIcoMod` / 定理 `continuousAt_toIcoMod`

English:
theorem continuousAt_toIcoMod
  given: (hx : ¬x ≡ a [PMOD p])
  statement: ContinuousAt (toIcoMod hp a) x
  proof: continuousAt_id.sub tendsto_nhds_of_eventually_eq
    (eventuallyEq_toIcoDiv_nhds hp a hx).fun_comp (· • p)

中文:
定理 continuousAt_toIcoMod
  条件: (hx : ¬x ≡ a [PMOD p])
  结论: ContinuousAt (toIcoMod hp a) x
  证明: continuousAt_id.sub tendsto_nhds_of_eventually_eq
    (eventuallyEq_toIcoDiv_nhds hp a hx).fun_comp (· • p)

Depends on / 依赖: continuousAt_id, continuousAt_id.sub, eventuallyEq_toIcoDiv_nhds, fun_comp, tendsto_nhds_of_eventually_eq
-/
theorem continuousAt_toIcoMod (hx : ¬x ≡ a [PMOD p]) : ContinuousAt (toIcoMod hp a) x :=
continuousAt_id.sub tendsto_nhds_of_eventually_eq
    (eventuallyEq_toIcoDiv_nhds hp a hx).fun_comp (· • p)

/--
theorem `continuousAt_toIocMod` / 定理 `continuousAt_toIocMod`

English:
theorem continuousAt_toIocMod
  given: (hx : ¬x ≡ a [PMOD p])
  statement: ContinuousAt (toIocMod hp a) x
  proof: continuousAt_id.sub tendsto_nhds_of_eventually_eq
    (eventuallyEq_toIocDiv_nhds hp a hx).fun_comp (· • p)

中文:
定理 continuousAt_toIocMod
  条件: (hx : ¬x ≡ a [PMOD p])
  结论: ContinuousAt (toIocMod hp a) x
  证明: continuousAt_id.sub tendsto_nhds_of_eventually_eq
    (eventuallyEq_toIocDiv_nhds hp a hx).fun_comp (· • p)

Depends on / 依赖: continuousAt_id, continuousAt_id.sub, eventuallyEq_toIocDiv_nhds, fun_comp, tendsto_nhds_of_eventually_eq
-/
theorem continuousAt_toIocMod (hx : ¬x ≡ a [PMOD p]) : ContinuousAt (toIocMod hp a) x :=
continuousAt_id.sub tendsto_nhds_of_eventually_eq
    (eventuallyEq_toIocDiv_nhds hp a hx).fun_comp (· • p)

end Continuity

/--
Definition of `AddCircle` / `AddCircle` 的定义

English:
abbreviation AddCircle
  signature: [AddCommGroup 𝕜] (p : 𝕜)
  body: 𝕜 ⧸ zmultiples p

中文:
缩写 AddCircle
  签名: [加法交换群 𝕜] (p : 𝕜)
  定义体: 𝕜 ⧸ zmultiples p

Depends on / 依赖: zmultiples
-/
abbrev AddCircle [AddCommGroup 𝕜] (p : 𝕜) :=
  𝕜 ⧸ zmultiples p

namespace AddCircle

section LinearOrderedAddCommGroup

variable [AddCommGroup 𝕜] (p : 𝕜)

/--
theorem `coe_nsmul` / 定理 `coe_nsmul`

English:
theorem coe_nsmul
  given: {n : Nat} {x : 𝕜}
  statement: (↑(n • x) : AddCircle p) = n • (x : AddCircle p)
  proof: rfl

中文:
定理 coe_nsmul
  条件: {n : 自然数} {x : 𝕜}
  结论: (↑(n • x) : AddCircle p) = n • (x : AddCircle p)
  证明: rfl
-/
theorem coe_nsmul {n : Nat} {x : 𝕜} : (↑(n • x) : AddCircle p) = n • (x : AddCircle p) :=
  rfl

/--
theorem `coe_zsmul` / 定理 `coe_zsmul`

English:
theorem coe_zsmul
  given: {n : Int} {x : 𝕜}
  statement: (↑(n • x) : AddCircle p) = n • (x : AddCircle p)
  proof: rfl

中文:
定理 coe_zsmul
  条件: {n : 整数} {x : 𝕜}
  结论: (↑(n • x) : AddCircle p) = n • (x : AddCircle p)
  证明: rfl
-/
theorem coe_zsmul {n : Int} {x : 𝕜} : (↑(n • x) : AddCircle p) = n • (x : AddCircle p) :=
  rfl

/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : 𝕜)
  statement: (↑(x + y) : AddCircle p) = (x : AddCircle p) + (y : AddCircle p)
  proof: rfl

中文:
定理 coe_add
  条件: (x y : 𝕜)
  结论: (↑(x + y) : AddCircle p) = (x : AddCircle p) + (y : AddCircle p)
  证明: rfl
-/
theorem coe_add (x y : 𝕜) : (↑(x + y) : AddCircle p) = (x : AddCircle p) + (y : AddCircle p) :=
  rfl

/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (x y : 𝕜)
  statement: (↑(x - y) : AddCircle p) = (x : AddCircle p) - (y : AddCircle p)
  proof: rfl

中文:
定理 coe_sub
  条件: (x y : 𝕜)
  结论: (↑(x - y) : AddCircle p) = (x : AddCircle p) - (y : AddCircle p)
  证明: rfl
-/
theorem coe_sub (x y : 𝕜) : (↑(x - y) : AddCircle p) = (x : AddCircle p) - (y : AddCircle p) :=
  rfl

/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: {x : 𝕜}
  statement: (↑(-x) : AddCircle p) = -(x : AddCircle p)
  proof: rfl

@[norm_cast]

中文:
定理 coe_neg
  条件: {x : 𝕜}
  结论: (↑(-x) : AddCircle p) = -(x : AddCircle p)
  证明: rfl

@[norm_cast]
-/
theorem coe_neg {x : 𝕜} : (↑(-x) : AddCircle p) = -(x : AddCircle p) :=
  rfl

@[norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ↑(0 : 𝕜) = (0 : AddCircle p)
  proof: rfl

中文:
定理 coe_zero
  结论: ↑(0 : 𝕜) = (0 : AddCircle p)
  证明: rfl
-/
theorem coe_zero : ↑(0 : 𝕜) = (0 : AddCircle p) :=
  rfl

/--
theorem `coe_eq_zero_iff` / 定理 `coe_eq_zero_iff`

English:
theorem coe_eq_zero_iff
  given: {x : 𝕜}
  statement: (x : AddCircle p) = 0 ↔ exists n : Int, n • p = x
  proof: by
  simp [AddSubgroup.mem_zmultiples_iff]

中文:
定理 coe_eq_zero_iff
  条件: {x : 𝕜}
  结论: (x : AddCircle p) = 0 ↔ 存在 n : 整数, n • p = x
  证明: by
  simp [AddSubgroup.mem_zmultiples_iff]

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_zmultiples_iff, mem_zmultiples_iff
-/
theorem coe_eq_zero_iff {x : 𝕜} : (x : AddCircle p) = 0 ↔ exists n : Int, n • p = x := by
  simp [AddSubgroup.mem_zmultiples_iff]

/--
theorem `coe_period` / 定理 `coe_period`

English:
theorem coe_period
  statement: (p : AddCircle p) = 0
  proof: (QuotientAddGroup.eq_zero_iff p).2 mem_zmultiples p

中文:
定理 coe_period
  结论: (p : AddCircle p) = 0
  证明: (QuotientAddGroup.eq_zero_iff p).2 mem_zmultiples p

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.eq_zero_iff, eq_zero_iff, mem_zmultiples
-/
theorem coe_period : (p : AddCircle p) = 0 :=
(QuotientAddGroup.eq_zero_iff p).2 mem_zmultiples p

/--
theorem `coe_add_period` / 定理 `coe_add_period`

English:
theorem coe_add_period
  given: (x : 𝕜)
  statement: ((x + p : 𝕜) : AddCircle p) = x
  proof: by
  rw [coe_add]; rw [← eq_sub_iff_add_eq']; rw [sub_self]; rw [coe_period]

@[continuity, nolint unusedArguments]

中文:
定理 coe_add_period
  条件: (x : 𝕜)
  结论: ((x + p : 𝕜) : AddCircle p) = x
  证明: by
  rw [coe_add]; rw [← eq_sub_iff_add_eq']; rw [sub_self]; rw [coe_period]

@[continuity, nolint unusedArguments]

Depends on / 依赖: coe_add, coe_period, eq_sub_iff_add_eq, sub_self
-/
theorem coe_add_period (x : 𝕜) : ((x + p : 𝕜) : AddCircle p) = x := by
  rw [coe_add]; rw [← eq_sub_iff_add_eq']; rw [sub_self]; rw [coe_period]

@[continuity, nolint unusedArguments]
/--
theorem `continuous_mk'` / 定理 `continuous_mk'`

English:
theorem continuous_mk'
  given: [TopologicalSpace 𝕜]
  proof: continuous_coinduced_rng

中文:
定理 continuous_mk'
  条件: [拓扑空间 𝕜]
  证明: continuous_coinduced_rng
-/
protected theorem continuous_mk' [TopologicalSpace 𝕜] :
    Continuous (QuotientAddGroup.mk' (zmultiples p) : 𝕜 -> AddCircle p) :=
  continuous_coinduced_rng

section Torsion

-- TODO: move this (and the definition `AddCircle`) to GroupTheory.QuotientGroup.Basic
open QuotientAddGroup Cardinal in
/--
theorem `card_torsion_le_of_isSMulRegular` / 定理 `card_torsion_le_of_isSMulRegular`

English:
theorem card_torsion_le_of_isSMulRegular
  given: (n : Nat) (h0 : n != 0) (hn : IsSMulRegular 𝕜 n)
  proof: by
  have (x : {x : AddCircle p | n • x = 0}) : exists (k : Fin n) (y : 𝕜), y = x.1 ∧ n • y = k.1 • p := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := mk_surjective x
    rw [Set.mem_ofPred]; rw [← mk_nsmul]; rw [eq_zero_iff] at hx
    have ⟨m', hm⟩ := hx
    have : NeZero n := ⟨h0⟩
    rw [← (Int.divModEquiv n).symm_apply_apply m']; rw [Int.divModEquiv_symm_apply] at hm
    set m := m'.divModEquiv n
    use m.2, y - m.1 • p
    simp_rw [mk_sub, mk_zsmul, sub_eq_self, coe_period, smul_zero]
    rw [smul_sub]; rw [sub_eq_iff_eq_add]; rw [← hm]; rw [add_comm]
    simp [add_smul, mul_comm, mul_smul]
  choose f hf using this
  refine (ENat.card_le_card_of_injective (f := f) fun x x' eq => Subtype.ext ?_).trans (by simp)
  have ⟨y, hyx, hy⟩ := hf x
  have ⟨y', hyx', hy'⟩ := hf x'
  rw [eq]; rw [← hy']; rw [hn.eq_iff] at hy
  rw [← hyx]; rw [hy]; rw [hyx']

中文:
定理 card_torsion_le_of_isSMulRegular
  条件: (n : 自然数) (h0 : n != 0) (hn : IsSMulRegular 𝕜 n)
  证明: by
  have (x : {x : AddCircle p | n • x = 0}) : exists (k : Fin n) (y : 𝕜), y = x.1 ∧ n • y = k.1 • p := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := mk_surjective x
    rw [Set.mem_ofPred]; rw [← mk_nsmul]; rw [eq_zero_iff] at hx
    have ⟨m', hm⟩ := hx
    have : NeZero n := ⟨h0⟩
    rw [← (Int.divModEquiv n).symm_apply_apply m']; rw [Int.divModEquiv_symm_apply] at hm
    set m := m'.divModEquiv n
    use m.2, y - m.1 • p
    simp_rw [mk_sub, mk_zsmul, sub_eq_self, coe_period, smul_zero]
    rw [smul_sub]; rw [sub_eq_iff_eq_add]; rw [← hm]; rw [add_comm]
    simp [add_smul, mul_comm, mul_smul]
  choose f hf using this
  refine (ENat.card_le_card_of_injective (f := f) fun x x' eq => Subtype.ext ?_).trans (by simp)
  have ⟨y, hyx, hy⟩ := hf x
  have ⟨y', hyx', hy'⟩ := hf x'
  rw [eq]; rw [← hy']; rw [hn.eq_iff] at hy
  rw [← hyx]; rw [hy]; rw [hyx']

Depends on / 依赖: AddCircle, Int.divModEquiv, Int.divModEquiv_symm_apply, NeZero, Set.mem_ofPred, coe_period, divModEquiv, divModEquiv_symm_apply, eq_zero_iff, mem_ofPred, mk_nsmul, mk_sub, mk_surjective, mk_zsmul, simp_rw, smul_sub, smul_zero, sub_eq_iff_eq_add, sub_eq_self, symm_apply_apply
-/
theorem card_torsion_le_of_isSMulRegular (n : Nat) (h0 : n != 0) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.encard <= n := by
  have (x : {x : AddCircle p | n • x = 0}) : exists (k : Fin n) (y : 𝕜), y = x.1 ∧ n • y = k.1 • p := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := mk_surjective x
    rw [Set.mem_ofPred]; rw [← mk_nsmul]; rw [eq_zero_iff] at hx
    have ⟨m', hm⟩ := hx
    have : NeZero n := ⟨h0⟩
    rw [← (Int.divModEquiv n).symm_apply_apply m']; rw [Int.divModEquiv_symm_apply] at hm
    set m := m'.divModEquiv n
    use m.2, y - m.1 • p
    simp_rw [mk_sub, mk_zsmul, sub_eq_self, coe_period, smul_zero]
    rw [smul_sub]; rw [sub_eq_iff_eq_add]; rw [← hm]; rw [add_comm]
    simp [add_smul, mul_comm, mul_smul]
  choose f hf using this
  refine (ENat.card_le_card_of_injective (f := f) fun x x' eq => Subtype.ext ?_).trans (by simp)
  have ⟨y, hyx, hy⟩ := hf x
  have ⟨y', hyx', hy'⟩ := hf x'
  rw [eq]; rw [← hy']; rw [hn.eq_iff] at hy
  rw [← hyx]; rw [hy]; rw [hyx']

/--
theorem `finite_torsion_of_isSMulRegular` / 定理 `finite_torsion_of_isSMulRegular`

English:
theorem finite_torsion_of_isSMulRegular
  given: (n : Nat) (hn : IsSMulRegular 𝕜 n)
  proof: by
  nontriviality 𝕜
  obtain rfl | h0 := eq_or_ne n 0
  exacts [hn.not_zero.elim, ENat.card_lt_top.mp <|
(card_torsion_le_of_isSMulRegular p n h0 hn).trans_lt ENat.natCast_lt_top n]

中文:
定理 finite_torsion_of_isSMulRegular
  条件: (n : 自然数) (hn : IsSMulRegular 𝕜 n)
  证明: by
  nontriviality 𝕜
  obtain rfl | h0 := eq_or_ne n 0
  exacts [hn.not_zero.elim, ENat.card_lt_top.mp <|
(card_torsion_le_of_isSMulRegular p n h0 hn).trans_lt ENat.natCast_lt_top n]

Depends on / 依赖: ENat.card_lt_top.mp, ENat.natCast_lt_top, card_lt_top, card_torsion_le_of_isSMulRegular, eq_or_ne, exacts, hn.not_zero.elim, natCast_lt_top, nontriviality, not_zero, trans_lt
-/
theorem finite_torsion_of_isSMulRegular (n : Nat) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.Finite := by
  nontriviality 𝕜
  obtain rfl | h0 := eq_or_ne n 0
  exacts [hn.not_zero.elim, ENat.card_lt_top.mp <|
(card_torsion_le_of_isSMulRegular p n h0 hn).trans_lt ENat.natCast_lt_top n]

/--
theorem `card_torsion_le_of_isSMulRegular_int` / 定理 `card_torsion_le_of_isSMulRegular_int`

English:
theorem card_torsion_le_of_isSMulRegular_int
  given: (n : Int) (h0 : n != 0) (hn : IsSMulRegular 𝕜 n)
  proof: by
  convert!
    card_torsion_le_of_isSMulRegular p _ (Int.natAbs_ne_zero.mpr h0)
      (IsSMulRegular.natAbs_iff.mpr hn) using 1
  simp

中文:
定理 card_torsion_le_of_isSMulRegular_int
  条件: (n : 整数) (h0 : n != 0) (hn : IsSMulRegular 𝕜 n)
  证明: by
  convert!
    card_torsion_le_of_isSMulRegular p _ (Int.natAbs_ne_zero.mpr h0)
      (IsSMulRegular.natAbs_iff.mpr hn) using 1
  simp

Depends on / 依赖: Int.natAbs_ne_zero.mpr, IsSMulRegular, IsSMulRegular.natAbs_iff.mpr, card_torsion_le_of_isSMulRegular, convert, natAbs_iff, natAbs_ne_zero
-/
theorem card_torsion_le_of_isSMulRegular_int (n : Int) (h0 : n != 0) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.encard <= n.natAbs := by
  convert!
    card_torsion_le_of_isSMulRegular p _ (Int.natAbs_ne_zero.mpr h0)
      (IsSMulRegular.natAbs_iff.mpr hn) using 1
  simp

/--
theorem `finite_torsion_of_isSMulRegular_int` / 定理 `finite_torsion_of_isSMulRegular_int`

English:
theorem finite_torsion_of_isSMulRegular_int
  given: (n : Int) (hn : IsSMulRegular 𝕜 n)
  proof: by
  nontriviality 𝕜
  obtain rfl | h0 := eq_or_ne n 0
  exacts [hn.not_zero.elim, ENat.card_lt_top.mp <|
(card_torsion_le_of_isSMulRegular_int p n h0 hn).trans_lt ENat.natCast_lt_top _]

中文:
定理 finite_torsion_of_isSMulRegular_int
  条件: (n : 整数) (hn : IsSMulRegular 𝕜 n)
  证明: by
  nontriviality 𝕜
  obtain rfl | h0 := eq_or_ne n 0
  exacts [hn.not_zero.elim, ENat.card_lt_top.mp <|
(card_torsion_le_of_isSMulRegular_int p n h0 hn).trans_lt ENat.natCast_lt_top _]

Depends on / 依赖: ENat.card_lt_top.mp, ENat.natCast_lt_top, card_lt_top, card_torsion_le_of_isSMulRegular_int, eq_or_ne, exacts, hn.not_zero.elim, natCast_lt_top, nontriviality, not_zero, trans_lt
-/
theorem finite_torsion_of_isSMulRegular_int (n : Int) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.Finite := by
  nontriviality 𝕜
  obtain rfl | h0 := eq_or_ne n 0
  exacts [hn.not_zero.elim, ENat.card_lt_top.mp <|
(card_torsion_le_of_isSMulRegular_int p n h0 hn).trans_lt ENat.natCast_lt_top _]

end Torsion

variable [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]

/--
theorem `finite_torsion` / 定理 `finite_torsion`

English:
theorem finite_torsion
  given: {n : Nat} (hn : 0 < n)
  statement: { u : AddCircle p | n • u = 0 }.Finite
  proof: finite_torsion_of_isSMulRegular _ _ .of_right_eq_zero_of_smul fun _ => by simp [hn.ne']

中文:
定理 finite_torsion
  条件: {n : 自然数} (hn : 0 < n)
  结论: { u : AddCircle p | n • u = 0 }.有限
  证明: finite_torsion_of_isSMulRegular _ _ .of_right_eq_zero_of_smul fun _ => by simp [hn.ne']

Depends on / 依赖: finite_torsion_of_isSMulRegular, hn.ne, of_right_eq_zero_of_smul
-/
theorem finite_torsion {n : Nat} (hn : 0 < n) : { u : AddCircle p | n • u = 0 }.Finite :=
finite_torsion_of_isSMulRegular _ _ .of_right_eq_zero_of_smul fun _ => by simp [hn.ne']

/--
theorem `finite_setOfPred_addOrderOf_eq` / 定理 `finite_setOfPred_addOrderOf_eq`

English:
theorem finite_setOfPred_addOrderOf_eq
  given: {n : Nat} (hn : 0 < n)
  proof: (finite_torsion p hn).subset fun _ h => ((addOrderOf_eq_iff hn).mp h).1

@[deprecated (since := "2026-07-09")]
alias finite_setOf_addOrderOf_eq := finite_setOfPred_addOrderOf_eq

中文:
定理 finite_setOfPred_addOrderOf_eq
  条件: {n : 自然数} (hn : 0 < n)
  证明: (finite_torsion p hn).subset fun _ h => ((addOrderOf_eq_iff hn).mp h).1

@[deprecated (since := "2026-07-09")]
alias finite_setOf_addOrderOf_eq := finite_setOfPred_addOrderOf_eq

Depends on / 依赖: addOrderOf_eq_iff, finite_torsion, subset
-/
theorem finite_setOfPred_addOrderOf_eq {n : Nat} (hn : 0 < n) :
    {u : AddCircle p | addOrderOf u = n}.Finite :=
  (finite_torsion p hn).subset fun _ h => ((addOrderOf_eq_iff hn).mp h).1

@[deprecated (since := "2026-07-09")]
alias finite_setOf_addOrderOf_eq := finite_setOfPred_addOrderOf_eq

/--
theorem `coe_eq_zero_of_pos_iff` / 定理 `coe_eq_zero_of_pos_iff`

English:
theorem coe_eq_zero_of_pos_iff
  given: (hp : 0 < p) {x : 𝕜} (hx : 0 < x)
  proof: by
  rw [coe_eq_zero_iff]
  constructor <;> rintro ⟨n, rfl⟩
  · replace hx : 0 < n := by
      contrapose! hx
      simpa only [← neg_nonneg, ← zsmul_neg, zsmul_neg'] using zsmul_nonneg hp.le (neg_nonneg.2 hx)
    exact ⟨n.toNat, by rw [← natCast_zsmul, Int.toNat_of_nonneg hx.le]⟩
  · exact ⟨(n : Int), by simp⟩

中文:
定理 coe_eq_zero_of_pos_iff
  条件: (hp : 0 < p) {x : 𝕜} (hx : 0 < x)
  证明: by
  rw [coe_eq_zero_iff]
  constructor <;> rintro ⟨n, rfl⟩
  · replace hx : 0 < n := by
      contrapose! hx
      simpa only [← neg_nonneg, ← zsmul_neg, zsmul_neg'] using zsmul_nonneg hp.le (neg_nonneg.2 hx)
    exact ⟨n.toNat, by rw [← natCast_zsmul, Int.toNat_of_nonneg hx.le]⟩
  · exact ⟨(n : Int), by simp⟩

Depends on / 依赖: Int.toNat_of_nonneg, coe_eq_zero_iff, contrapose, hp.le, hx.le, n.toNat, natCast_zsmul, neg_nonneg, replace, toNat_of_nonneg, zsmul_neg, zsmul_nonneg
-/
theorem coe_eq_zero_of_pos_iff (hp : 0 < p) {x : 𝕜} (hx : 0 < x) :
    (x : AddCircle p) = 0 ↔ exists n : Nat, n • p = x := by
  rw [coe_eq_zero_iff]
  constructor <;> rintro ⟨n, rfl⟩
  · replace hx : 0 < n := by
      contrapose! hx
      simpa only [← neg_nonneg, ← zsmul_neg, zsmul_neg'] using zsmul_nonneg hp.le (neg_nonneg.2 hx)
    exact ⟨n.toNat, by rw [← natCast_zsmul, Int.toNat_of_nonneg hx.le]⟩
  · exact ⟨(n : Int), by simp⟩

variable [hp : Fact (0 < p)] (a : 𝕜) [Archimedean 𝕜]

/--
Definition of `equivIco` / `equivIco` 的定义

English:
definition equivIco
  signature: : AddCircle p ≃ Ico a (a + p)
  body: QuotientAddGroup.equivIcoMod hp.out a

中文:
定义 equivIco
  签名: : AddCircle p ≃ 左闭右开区间 a (a + p)
  定义体: QuotientAddGroup.equivIcoMod hp.out a

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.equivIcoMod, equivIcoMod, hp.out
-/
def equivIco : AddCircle p ≃ Ico a (a + p) :=
  QuotientAddGroup.equivIcoMod hp.out a

/--
Definition of `equivIoc` / `equivIoc` 的定义

English:
definition equivIoc
  signature: : AddCircle p ≃ Ioc a (a + p)
  body: QuotientAddGroup.equivIocMod hp.out a

中文:
定义 equivIoc
  签名: : AddCircle p ≃ 左开右闭区间 a (a + p)
  定义体: QuotientAddGroup.equivIocMod hp.out a

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.equivIocMod, equivIocMod, hp.out
-/
def equivIoc : AddCircle p ≃ Ioc a (a + p) :=
  QuotientAddGroup.equivIocMod hp.out a

/--
Definition of `liftIco` / `liftIco` 的定义

English:
definition liftIco
  signature: (f : 𝕜 -> B)
  body: domRestrict _ f ∘ AddCircle.equivIco p a

中文:
定义 liftIco
  签名: (f : 𝕜 -> B)
  定义体: domRestrict _ f ∘ AddCircle.equivIco p a

Depends on / 依赖: AddCircle, AddCircle.equivIco, domRestrict, equivIco
-/
def liftIco (f : 𝕜 -> B) : AddCircle p -> B :=
  domRestrict _ f ∘ AddCircle.equivIco p a

/--
Definition of `liftIoc` / `liftIoc` 的定义

English:
definition liftIoc
  signature: (f : 𝕜 -> B)
  body: domRestrict _ f ∘ AddCircle.equivIoc p a

中文:
定义 liftIoc
  签名: (f : 𝕜 -> B)
  定义体: domRestrict _ f ∘ AddCircle.equivIoc p a

Depends on / 依赖: AddCircle, AddCircle.equivIoc, domRestrict, equivIoc
-/
def liftIoc (f : 𝕜 -> B) : AddCircle p -> B :=
  domRestrict _ f ∘ AddCircle.equivIoc p a

variable {p a}

/--
theorem `equivIco_coe_eq` / 定理 `equivIco_coe_eq`

English:
theorem equivIco_coe_eq
  given: {x : 𝕜} (hx : x in Ico a (a + p))
  statement: (equivIco p a) x = ⟨x, hx⟩
  proof: by
  rw [← Equiv.eq_symm_apply]; rw [equivIco]; rw [QuotientAddGroup.equivIcoMod_symm_apply]

中文:
定理 equivIco_coe_eq
  条件: {x : 𝕜} (hx : x in 左闭右开区间 a (a + p))
  结论: (equivIco p a) x = ⟨x, hx⟩
  证明: by
  rw [← Equiv.eq_symm_apply]; rw [equivIco]; rw [QuotientAddGroup.equivIcoMod_symm_apply]

Depends on / 依赖: Equiv.eq_symm_apply, QuotientAddGroup, QuotientAddGroup.equivIcoMod_symm_apply, eq_symm_apply, equivIco, equivIcoMod_symm_apply
-/
theorem equivIco_coe_eq {x : 𝕜} (hx : x in Ico a (a + p)) : (equivIco p a) x = ⟨x, hx⟩ := by
  rw [← Equiv.eq_symm_apply]; rw [equivIco]; rw [QuotientAddGroup.equivIcoMod_symm_apply]

/--
theorem `equivIoc_coe_eq` / 定理 `equivIoc_coe_eq`

English:
theorem equivIoc_coe_eq
  given: {x : 𝕜} (hx : x in Ioc a (a + p))
  statement: (equivIoc p a) x = ⟨x, hx⟩
  proof: by
  rw [← Equiv.eq_symm_apply]; rw [equivIoc]; rw [QuotientAddGroup.equivIocMod_symm_apply]

@[simp]

中文:
定理 equivIoc_coe_eq
  条件: {x : 𝕜} (hx : x in 左开右闭区间 a (a + p))
  结论: (equivIoc p a) x = ⟨x, hx⟩
  证明: by
  rw [← Equiv.eq_symm_apply]; rw [equivIoc]; rw [QuotientAddGroup.equivIocMod_symm_apply]

@[simp]

Depends on / 依赖: Equiv.eq_symm_apply, QuotientAddGroup, QuotientAddGroup.equivIocMod_symm_apply, eq_symm_apply, equivIoc, equivIocMod_symm_apply
-/
theorem equivIoc_coe_eq {x : 𝕜} (hx : x in Ioc a (a + p)) : (equivIoc p a) x = ⟨x, hx⟩ := by
  rw [← Equiv.eq_symm_apply]; rw [equivIoc]; rw [QuotientAddGroup.equivIocMod_symm_apply]

@[simp]
/--
lemma `coe_equivIco` / 引理 `coe_equivIco`

English:
lemma coe_equivIco
  given: {y : AddCircle p}
  proof: (equivIco p a).left_inv y

@[simp]

中文:
引理 coe_equivIco
  条件: {y : AddCircle p}
  证明: (equivIco p a).left_inv y

@[simp]

Depends on / 依赖: equivIco, left_inv
-/
lemma coe_equivIco {y : AddCircle p} :
    (equivIco p a y : AddCircle p) = y :=
  (equivIco p a).left_inv y

@[simp]
/--
lemma `coe_equivIoc` / 引理 `coe_equivIoc`

English:
lemma coe_equivIoc
  given: {y : AddCircle p}
  proof: (equivIoc p a).left_inv y

中文:
引理 coe_equivIoc
  条件: {y : AddCircle p}
  证明: (equivIoc p a).left_inv y

Depends on / 依赖: equivIoc, left_inv
-/
lemma coe_equivIoc {y : AddCircle p} :
    (equivIoc p a y : AddCircle p) = y :=
  (equivIoc p a).left_inv y

/--
lemma `equivIco_coe_of_mem` / 引理 `equivIco_coe_of_mem`

English:
lemma equivIco_coe_of_mem
  given: {y : 𝕜} (hy : y in Ico a (a + p))
  proof: by
  have : equivIco p a y = ⟨y, hy⟩ := (equivIco p a).right_inv ⟨y, hy⟩
  simp [this]

中文:
引理 equivIco_coe_of_mem
  条件: {y : 𝕜} (hy : y in 左闭右开区间 a (a + p))
  证明: by
  have : equivIco p a y = ⟨y, hy⟩ := (equivIco p a).right_inv ⟨y, hy⟩
  simp [this]

Depends on / 依赖: equivIco, right_inv
-/
lemma equivIco_coe_of_mem {y : 𝕜} (hy : y in Ico a (a + p)) :
    equivIco p a y = y := by
  have : equivIco p a y = ⟨y, hy⟩ := (equivIco p a).right_inv ⟨y, hy⟩
  simp [this]

/--
lemma `equivIoc_coe_of_mem` / 引理 `equivIoc_coe_of_mem`

English:
lemma equivIoc_coe_of_mem
  given: {y : 𝕜} (hy : y in Ioc a (a + p))
  proof: by
  have : equivIoc p a y = ⟨y, hy⟩ := (equivIoc p a).right_inv ⟨y, hy⟩
  simp [this]

中文:
引理 equivIoc_coe_of_mem
  条件: {y : 𝕜} (hy : y in 左开右闭区间 a (a + p))
  证明: by
  have : equivIoc p a y = ⟨y, hy⟩ := (equivIoc p a).right_inv ⟨y, hy⟩
  simp [this]

Depends on / 依赖: equivIoc, right_inv
-/
lemma equivIoc_coe_of_mem {y : 𝕜} (hy : y in Ioc a (a + p)) :
    equivIoc p a y = y := by
  have : equivIoc p a y = ⟨y, hy⟩ := (equivIoc p a).right_inv ⟨y, hy⟩
  simp [this]

/--
theorem `coe_eq_coe_iff_of_mem_Ico` / 定理 `coe_eq_coe_iff_of_mem_Ico`

English:
theorem coe_eq_coe_iff_of_mem_Ico
  given: {x y : 𝕜} (hx : x in Ico a (a + p)) (hy : y in Ico a (a + p))
  proof: by
  refine ⟨fun h => ?_, by tauto⟩
  suffices (⟨x, hx⟩ : Ico a (a + p)) = ⟨y, hy⟩ by exact Subtype.mk.inj this
  apply_fun equivIco p a at h
  rw [← (equivIco p a).right_inv ⟨x]; rw [hx⟩]; rw [← (equivIco p a).right_inv ⟨y]; rw [hy⟩]
  exact h

中文:
定理 coe_eq_coe_iff_of_mem_Ico
  条件: {x y : 𝕜} (hx : x in 左闭右开区间 a (a + p)) (hy : y in 左闭右开区间 a (a + p))
  证明: by
  refine ⟨fun h => ?_, by tauto⟩
  suffices (⟨x, hx⟩ : Ico a (a + p)) = ⟨y, hy⟩ by exact Subtype.mk.inj this
  apply_fun equivIco p a at h
  rw [← (equivIco p a).right_inv ⟨x]; rw [hx⟩]; rw [← (equivIco p a).right_inv ⟨y]; rw [hy⟩]
  exact h

Depends on / 依赖: Subtype, Subtype.mk.inj, apply_fun, equivIco, right_inv
-/
theorem coe_eq_coe_iff_of_mem_Ico {x y : 𝕜} (hx : x in Ico a (a + p)) (hy : y in Ico a (a + p)) :
    (x : AddCircle p) = y ↔ x = y := by
  refine ⟨fun h => ?_, by tauto⟩
  suffices (⟨x, hx⟩ : Ico a (a + p)) = ⟨y, hy⟩ by exact Subtype.mk.inj this
  apply_fun equivIco p a at h
  rw [← (equivIco p a).right_inv ⟨x]; rw [hx⟩]; rw [← (equivIco p a).right_inv ⟨y]; rw [hy⟩]
  exact h

/--
lemma `coe_eq_coe_iff_of_mem_Ioc` / 引理 `coe_eq_coe_iff_of_mem_Ioc`

English:
lemma coe_eq_coe_iff_of_mem_Ioc
  given: {x y : 𝕜} (hx : x in Ioc a (a + p)) (hy : y in Ioc a (a + p))
  proof: by
  refine ⟨fun h => ?_, by tauto⟩
  suffices (⟨x, hx⟩ : Ioc a (a + p)) = ⟨y, hy⟩ by exact Subtype.mk.inj this
  apply_fun equivIoc p a at h
  rw [← (equivIoc p a).right_inv ⟨x]; rw [hx⟩]; rw [← (equivIoc p a).right_inv ⟨y]; rw [hy⟩]
  exact h

中文:
引理 coe_eq_coe_iff_of_mem_Ioc
  条件: {x y : 𝕜} (hx : x in 左开右闭区间 a (a + p)) (hy : y in 左开右闭区间 a (a + p))
  证明: by
  refine ⟨fun h => ?_, by tauto⟩
  suffices (⟨x, hx⟩ : Ioc a (a + p)) = ⟨y, hy⟩ by exact Subtype.mk.inj this
  apply_fun equivIoc p a at h
  rw [← (equivIoc p a).right_inv ⟨x]; rw [hx⟩]; rw [← (equivIoc p a).right_inv ⟨y]; rw [hy⟩]
  exact h

Depends on / 依赖: Subtype, Subtype.mk.inj, apply_fun, equivIoc, right_inv
-/
lemma coe_eq_coe_iff_of_mem_Ioc {x y : 𝕜} (hx : x in Ioc a (a + p)) (hy : y in Ioc a (a + p)) :
    (x : AddCircle p) = y ↔ x = y := by
  refine ⟨fun h => ?_, by tauto⟩
  suffices (⟨x, hx⟩ : Ioc a (a + p)) = ⟨y, hy⟩ by exact Subtype.mk.inj this
  apply_fun equivIoc p a at h
  rw [← (equivIoc p a).right_inv ⟨x]; rw [hx⟩]; rw [← (equivIoc p a).right_inv ⟨y]; rw [hy⟩]
  exact h

/--
theorem `liftIco_coe_apply` / 定理 `liftIco_coe_apply`

English:
theorem liftIco_coe_apply
  given: {f : 𝕜 -> B} {x : 𝕜} (hx : x in Ico a (a + p))
  proof: by
  simp [liftIco, equivIco_coe_eq hx]

中文:
定理 liftIco_coe_apply
  条件: {f : 𝕜 -> B} {x : 𝕜} (hx : x in 左闭右开区间 a (a + p))
  证明: by
  simp [liftIco, equivIco_coe_eq hx]

Depends on / 依赖: equivIco_coe_eq, liftIco
-/
theorem liftIco_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx : x in Ico a (a + p)) :
    liftIco p a f ↑x = f x := by
  simp [liftIco, equivIco_coe_eq hx]

/--
theorem `liftIoc_coe_apply` / 定理 `liftIoc_coe_apply`

English:
theorem liftIoc_coe_apply
  given: {f : 𝕜 -> B} {x : 𝕜} (hx : x in Ioc a (a + p))
  proof: by
  simp [liftIoc, equivIoc_coe_eq hx]

中文:
定理 liftIoc_coe_apply
  条件: {f : 𝕜 -> B} {x : 𝕜} (hx : x in 左开右闭区间 a (a + p))
  证明: by
  simp [liftIoc, equivIoc_coe_eq hx]

Depends on / 依赖: equivIoc_coe_eq, liftIoc
-/
theorem liftIoc_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx : x in Ioc a (a + p)) :
    liftIoc p a f ↑x = f x := by
  simp [liftIoc, equivIoc_coe_eq hx]

/--
theorem `liftIoc_eq_liftIco_of_ne` / 定理 `liftIoc_eq_liftIco_of_ne`

English:
theorem liftIoc_eq_liftIco_of_ne
  statement: {f : 𝕜 -> B} {x : AddCircle p}
  proof: by
  have x_eq_b : x = ↑(equivIco p a x) := coe_equivIco.symm
  rw [x_eq_b]; rw [liftIco_coe_apply (equivIco p a x).coe_prop]
  exact liftIoc_coe_apply (by grind)

中文:
定理 liftIoc_eq_liftIco_of_ne
  结论: {f : 𝕜 -> B} {x : AddCircle p}
  证明: by
  have x_eq_b : x = ↑(equivIco p a x) := coe_equivIco.symm
  rw [x_eq_b]; rw [liftIco_coe_apply (equivIco p a x).coe_prop]
  exact liftIoc_coe_apply (by grind)

Depends on / 依赖: coe_equivIco, coe_equivIco.symm, coe_prop, equivIco, liftIco_coe_apply, liftIoc_coe_apply, x_eq_b
-/
theorem liftIoc_eq_liftIco_of_ne {f : 𝕜 -> B} {x : AddCircle p}
    (x_ne_a : x != a) : liftIoc p a f x = liftIco p a f x := by
  have x_eq_b : x = ↑(equivIco p a x) := coe_equivIco.symm
  rw [x_eq_b]; rw [liftIco_coe_apply (equivIco p a x).coe_prop]
  exact liftIoc_coe_apply (by grind)

/--
lemma `liftIco_comp_apply` / 引理 `liftIco_comp_apply`

English:
lemma liftIco_comp_apply
  given: {α β : Type*} {f : 𝕜 -> α} {g : α -> β} {a : 𝕜} {x : AddCircle p}
  proof: rfl

中文:
引理 liftIco_comp_apply
  条件: {α β : 类型} {f : 𝕜 -> α} {g : α -> β} {a : 𝕜} {x : AddCircle p}
  证明: rfl
-/
lemma liftIco_comp_apply {α β : Type*} {f : 𝕜 -> α} {g : α -> β} {a : 𝕜} {x : AddCircle p} :
    liftIco p a (g ∘ f) x = g (liftIco p a f x) := rfl

/--
lemma `liftIoc_comp_apply` / 引理 `liftIoc_comp_apply`

English:
lemma liftIoc_comp_apply
  given: {α β : Type*} {f : 𝕜 -> α} {g : α -> β} {a : 𝕜} {x : AddCircle p}
  proof: rfl

中文:
引理 liftIoc_comp_apply
  条件: {α β : 类型} {f : 𝕜 -> α} {g : α -> β} {a : 𝕜} {x : AddCircle p}
  证明: rfl
-/
lemma liftIoc_comp_apply {α β : Type*} {f : 𝕜 -> α} {g : α -> β} {a : 𝕜} {x : AddCircle p} :
    liftIoc p a (g ∘ f) x = g (liftIoc p a f x) := rfl

/--
lemma `eq_coe_Ico` / 引理 `eq_coe_Ico`

English:
lemma eq_coe_Ico
  given: (a : AddCircle p)
  statement: exists b in Ico 0 p, ↑b = a
  proof: by
  let b := QuotientAddGroup.equivIcoMod hp.out 0 a
  exact ⟨b.1, by simpa only [zero_add] using b.2,
    (QuotientAddGroup.equivIcoMod hp.out 0).symm_apply_apply a⟩

中文:
引理 eq_coe_Ico
  条件: (a : AddCircle p)
  结论: 存在 b in 左闭右开区间 0 p, ↑b = a
  证明: by
  let b := QuotientAddGroup.equivIcoMod hp.out 0 a
  exact ⟨b.1, by simpa only [zero_add] using b.2,
    (QuotientAddGroup.equivIcoMod hp.out 0).symm_apply_apply a⟩

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.equivIcoMod, equivIcoMod, hp.out, symm_apply_apply, zero_add
-/
lemma eq_coe_Ico (a : AddCircle p) : exists b in Ico 0 p, ↑b = a := by
  let b := QuotientAddGroup.equivIcoMod hp.out 0 a
  exact ⟨b.1, by simpa only [zero_add] using b.2,
    (QuotientAddGroup.equivIcoMod hp.out 0).symm_apply_apply a⟩

/--
lemma `eq_coe_Ioc` / 引理 `eq_coe_Ioc`

English:
lemma eq_coe_Ioc
  given: (a : AddCircle p)
  statement: exists b in Ioc 0 p, ↑b = a
  proof: by
  let b := QuotientAddGroup.equivIocMod hp.out 0 a
  exact ⟨b.1, by simpa only [zero_add] using b.2,
    (QuotientAddGroup.equivIocMod hp.out 0).symm_apply_apply a⟩

中文:
引理 eq_coe_Ioc
  条件: (a : AddCircle p)
  结论: 存在 b in 左开右闭区间 0 p, ↑b = a
  证明: by
  let b := QuotientAddGroup.equivIocMod hp.out 0 a
  exact ⟨b.1, by simpa only [zero_add] using b.2,
    (QuotientAddGroup.equivIocMod hp.out 0).symm_apply_apply a⟩

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.equivIocMod, equivIocMod, hp.out, symm_apply_apply, zero_add
-/
lemma eq_coe_Ioc (a : AddCircle p) : exists b in Ioc 0 p, ↑b = a := by
  let b := QuotientAddGroup.equivIocMod hp.out 0 a
  exact ⟨b.1, by simpa only [zero_add] using b.2,
    (QuotientAddGroup.equivIocMod hp.out 0).symm_apply_apply a⟩

/--
lemma `coe_eq_zero_iff_of_mem_Ico` / 引理 `coe_eq_zero_iff_of_mem_Ico`

English:
lemma coe_eq_zero_iff_of_mem_Ico
  given: (ha : a in Ico 0 p)
  proof: by
  have h0 : 0 in Ico 0 (0 + p) := by simpa [zero_add, left_mem_Ico] using hp.out
  have ha' : a in Ico 0 (0 + p) := by rwa [zero_add]
  rw [← AddCircle.coe_eq_coe_iff_of_mem_Ico ha' h0]; rw [QuotientAddGroup.mk_zero]

中文:
引理 coe_eq_zero_iff_of_mem_Ico
  条件: (ha : a in 左闭右开区间 0 p)
  证明: by
  have h0 : 0 in Ico 0 (0 + p) := by simpa [zero_add, left_mem_Ico] using hp.out
  have ha' : a in Ico 0 (0 + p) := by rwa [zero_add]
  rw [← AddCircle.coe_eq_coe_iff_of_mem_Ico ha' h0]; rw [QuotientAddGroup.mk_zero]

Depends on / 依赖: AddCircle, AddCircle.coe_eq_coe_iff_of_mem_Ico, QuotientAddGroup, QuotientAddGroup.mk_zero, coe_eq_coe_iff_of_mem_Ico, hp.out, left_mem_Ico, mk_zero, zero_add
-/
lemma coe_eq_zero_iff_of_mem_Ico (ha : a in Ico 0 p) :
    (a : AddCircle p) = 0 ↔ a = 0 := by
  have h0 : 0 in Ico 0 (0 + p) := by simpa [zero_add, left_mem_Ico] using hp.out
  have ha' : a in Ico 0 (0 + p) := by rwa [zero_add]
  rw [← AddCircle.coe_eq_coe_iff_of_mem_Ico ha' h0]; rw [QuotientAddGroup.mk_zero]

variable (p a)

section Continuity

variable [TopologicalSpace 𝕜]

@[continuity]
/--
theorem `continuous_equivIco_symm` / 定理 `continuous_equivIco_symm`

English:
theorem continuous_equivIco_symm
  statement: Continuous (equivIco p a).symm
  proof: continuous_quotient_mk'.comp continuous_subtype_val

@[continuity]

中文:
定理 continuous_equivIco_symm
  结论: 连续 (equivIco p a).symm
  证明: continuous_quotient_mk'.comp continuous_subtype_val

@[continuity]

Depends on / 依赖: continuous_quotient_mk, continuous_subtype_val
-/
theorem continuous_equivIco_symm : Continuous (equivIco p a).symm :=
  continuous_quotient_mk'.comp continuous_subtype_val

@[continuity]
/--
theorem `continuous_equivIoc_symm` / 定理 `continuous_equivIoc_symm`

English:
theorem continuous_equivIoc_symm
  statement: Continuous (equivIoc p a).symm
  proof: continuous_quotient_mk'.comp continuous_subtype_val

中文:
定理 continuous_equivIoc_symm
  结论: 连续 (equivIoc p a).symm
  证明: continuous_quotient_mk'.comp continuous_subtype_val

Depends on / 依赖: continuous_quotient_mk, continuous_subtype_val
-/
theorem continuous_equivIoc_symm : Continuous (equivIoc p a).symm :=
  continuous_quotient_mk'.comp continuous_subtype_val

variable [OrderTopology 𝕜] {x : AddCircle p}

/--
theorem `continuousAt_equivIco` / 定理 `continuousAt_equivIco`

English:
theorem continuousAt_equivIco
  given: (hx : x != a)
  statement: ContinuousAt (equivIco p a) x
  proof: by
  induction x using QuotientAddGroup.induction_on
  rw [ContinuousAt]; rw [Filter.Tendsto]; rw [QuotientAddGroup.nhds_eq]; rw [Filter.map_map]
  exact (continuousAt_toIcoMod hp.out a <| not_modEq_iff_ne_mod_zmultiples.mpr hx).codRestrict _

中文:
定理 continuousAt_equivIco
  条件: (hx : x != a)
  结论: ContinuousAt (equivIco p a) x
  证明: by
  induction x using QuotientAddGroup.induction_on
  rw [ContinuousAt]; rw [Filter.Tendsto]; rw [QuotientAddGroup.nhds_eq]; rw [Filter.map_map]
  exact (continuousAt_toIcoMod hp.out a <| not_modEq_iff_ne_mod_zmultiples.mpr hx).codRestrict _

Depends on / 依赖: ContinuousAt, Filter, Filter.Tendsto, Filter.map_map, QuotientAddGroup, QuotientAddGroup.induction_on, QuotientAddGroup.nhds_eq, Tendsto, codRestrict, continuousAt_toIcoMod, hp.out, induction_on, map_map, nhds_eq, not_modEq_iff_ne_mod_zmultiples, not_modEq_iff_ne_mod_zmultiples.mpr
-/
theorem continuousAt_equivIco (hx : x != a) : ContinuousAt (equivIco p a) x := by
  induction x using QuotientAddGroup.induction_on
  rw [ContinuousAt]; rw [Filter.Tendsto]; rw [QuotientAddGroup.nhds_eq]; rw [Filter.map_map]
  exact (continuousAt_toIcoMod hp.out a <| not_modEq_iff_ne_mod_zmultiples.mpr hx).codRestrict _

/--
theorem `continuousAt_equivIoc` / 定理 `continuousAt_equivIoc`

English:
theorem continuousAt_equivIoc
  given: (hx : x != a)
  statement: ContinuousAt (equivIoc p a) x
  proof: by
  induction x using QuotientAddGroup.induction_on
  rw [ContinuousAt]; rw [Filter.Tendsto]; rw [QuotientAddGroup.nhds_eq]; rw [Filter.map_map]
  exact (continuousAt_toIocMod hp.out a <| not_modEq_iff_ne_mod_zmultiples.mpr hx).codRestrict _

中文:
定理 continuousAt_equivIoc
  条件: (hx : x != a)
  结论: ContinuousAt (equivIoc p a) x
  证明: by
  induction x using QuotientAddGroup.induction_on
  rw [ContinuousAt]; rw [Filter.Tendsto]; rw [QuotientAddGroup.nhds_eq]; rw [Filter.map_map]
  exact (continuousAt_toIocMod hp.out a <| not_modEq_iff_ne_mod_zmultiples.mpr hx).codRestrict _

Depends on / 依赖: ContinuousAt, Filter, Filter.Tendsto, Filter.map_map, QuotientAddGroup, QuotientAddGroup.induction_on, QuotientAddGroup.nhds_eq, Tendsto, codRestrict, continuousAt_toIocMod, hp.out, induction_on, map_map, nhds_eq, not_modEq_iff_ne_mod_zmultiples, not_modEq_iff_ne_mod_zmultiples.mpr
-/
theorem continuousAt_equivIoc (hx : x != a) : ContinuousAt (equivIoc p a) x := by
  induction x using QuotientAddGroup.induction_on
  rw [ContinuousAt]; rw [Filter.Tendsto]; rw [QuotientAddGroup.nhds_eq]; rw [Filter.map_map]
  exact (continuousAt_toIocMod hp.out a <| not_modEq_iff_ne_mod_zmultiples.mpr hx).codRestrict _

/--
Definition of `openPartialHomeomorphCoe` / `openPartialHomeomorphCoe` 的定义

English:
definition openPartialHomeomorphCoe
  signature: [DiscreteTopology (zmultiples p)]
  body: (↑)
  invFun := fun x => equivIco p a x
  source := Ioo a (a + p)
  target := {↑a}ᶜ
  map_source' := by
    intro x hx hx'
    exact hx.1.ne' ((coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hx)
      (left_mem_Ico.mpr (lt_add_of_pos_right a hp.out))).mp hx')
  map_target' := by
    intro x hx
    exact (eq_left_or_mem_Ioo_of_mem_Ico (equivIco p a x).2).resolve_left
      (hx ∘ ((equivIco p a).symm_apply_apply x).symm.trans ∘ congrArg _)
  left_inv' :=
    fun x hx => congrArg _ ((equivIco p a).apply_symm_apply ⟨x, Ioo_subset_Ico_self hx⟩)
  right_inv' := fun x _ => (equivIco p a).symm_apply_apply x
  open_source := isOpen_Ioo
  open_target := isOpen_compl_singleton
  continuousOn_toFun := (AddCircle.continuous_mk' p).continuousOn
  continuousOn_invFun := by
    exact continuousOn_of_forall_continuousAt
      (fun _ => continuousAt_subtype_val.comp ∘ continuousAt_equivIco p a)

中文:
定义 openPartialHomeomorphCoe
  签名: [离散拓扑 (zmultiples p)]
  定义体: (↑)
  invFun := fun x => equivIco p a x
  source := Ioo a (a + p)
  target := {↑a}ᶜ
  map_source' := by
    intro x hx hx'
    exact hx.1.ne' ((coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hx)
      (left_mem_Ico.mpr (lt_add_of_pos_right a hp.out))).mp hx')
  map_target' := by
    intro x hx
    exact (eq_left_or_mem_Ioo_of_mem_Ico (equivIco p a x).2).resolve_left
      (hx ∘ ((equivIco p a).symm_apply_apply x).symm.trans ∘ congrArg _)
  left_inv' :=
    fun x hx => congrArg _ ((equivIco p a).apply_symm_apply ⟨x, Ioo_subset_Ico_self hx⟩)
  right_inv' := fun x _ => (equivIco p a).symm_apply_apply x
  open_source := isOpen_Ioo
  open_target := isOpen_compl_singleton
  continuousOn_toFun := (AddCircle.continuous_mk' p).continuousOn
  continuousOn_invFun := by
    exact continuousOn_of_forall_continuousAt
      (fun _ => continuousAt_subtype_val.comp ∘ continuousAt_equivIco p a)
-/
@[simps] def openPartialHomeomorphCoe [DiscreteTopology (zmultiples p)] :
    OpenPartialHomeomorph 𝕜 (AddCircle p) where
  toFun := (↑)
  invFun := fun x => equivIco p a x
  source := Ioo a (a + p)
  target := {↑a}ᶜ
  map_source' := by
    intro x hx hx'
    exact hx.1.ne' ((coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hx)
      (left_mem_Ico.mpr (lt_add_of_pos_right a hp.out))).mp hx')
  map_target' := by
    intro x hx
    exact (eq_left_or_mem_Ioo_of_mem_Ico (equivIco p a x).2).resolve_left
      (hx ∘ ((equivIco p a).symm_apply_apply x).symm.trans ∘ congrArg _)
  left_inv' :=
    fun x hx => congrArg _ ((equivIco p a).apply_symm_apply ⟨x, Ioo_subset_Ico_self hx⟩)
  right_inv' := fun x _ => (equivIco p a).symm_apply_apply x
  open_source := isOpen_Ioo
  open_target := isOpen_compl_singleton
  continuousOn_toFun := (AddCircle.continuous_mk' p).continuousOn
  continuousOn_invFun := by
    exact continuousOn_of_forall_continuousAt
      (fun _ => continuousAt_subtype_val.comp ∘ continuousAt_equivIco p a)

end Continuity

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → AddCircle p` is
the entire space. -/
@[simp]
/--
theorem `coe_image_Ico_eq` / 定理 `coe_image_Ico_eq`

English:
theorem coe_image_Ico_eq
  statement: ((↑) : 𝕜 -> AddCircle p) '' Ico a (a + p) = univ
  proof: by
  rw [image_eq_range]
  exact (equivIco p a).symm.range_eq_univ

中文:
定理 coe_image_Ico_eq
  结论: ((↑) : 𝕜 -> AddCircle p) '' 左闭右开区间 a (a + p) = univ
  证明: by
  rw [image_eq_range]
  exact (equivIco p a).symm.range_eq_univ

Depends on / 依赖: equivIco, image_eq_range, range_eq_univ, symm.range_eq_univ
-/
theorem coe_image_Ico_eq : ((↑) : 𝕜 -> AddCircle p) '' Ico a (a + p) = univ := by
  rw [image_eq_range]
  exact (equivIco p a).symm.range_eq_univ

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → AddCircle p` is
the entire space. -/
@[simp]
/--
theorem `coe_image_Ioc_eq` / 定理 `coe_image_Ioc_eq`

English:
theorem coe_image_Ioc_eq
  statement: ((↑) : 𝕜 -> AddCircle p) '' Ioc a (a + p) = univ
  proof: by
  rw [image_eq_range]
  exact (equivIoc p a).symm.range_eq_univ

中文:
定理 coe_image_Ioc_eq
  结论: ((↑) : 𝕜 -> AddCircle p) '' 左开右闭区间 a (a + p) = univ
  证明: by
  rw [image_eq_range]
  exact (equivIoc p a).symm.range_eq_univ

Depends on / 依赖: equivIoc, image_eq_range, range_eq_univ, symm.range_eq_univ
-/
theorem coe_image_Ioc_eq : ((↑) : 𝕜 -> AddCircle p) '' Ioc a (a + p) = univ := by
  rw [image_eq_range]
  exact (equivIoc p a).symm.range_eq_univ

/-- The image of the closed interval `[0, p]` under the quotient map `𝕜 → AddCircle p` is the
entire space. -/
@[simp]
/--
theorem `coe_image_Icc_eq` / 定理 `coe_image_Icc_eq`

English:
theorem coe_image_Icc_eq
  statement: ((↑) : 𝕜 -> AddCircle p) '' Icc a (a + p) = univ
  proof: eq_top_mono (image_mono Ico_subset_Icc_self) coe_image_Ico_eq _ _

中文:
定理 coe_image_Icc_eq
  结论: ((↑) : 𝕜 -> AddCircle p) '' 闭区间 a (a + p) = univ
  证明: eq_top_mono (image_mono Ico_subset_Icc_self) coe_image_Ico_eq _ _

Depends on / 依赖: Ico_subset_Icc_self, coe_image_Ico_eq, eq_top_mono, image_mono
-/
theorem coe_image_Icc_eq : ((↑) : 𝕜 -> AddCircle p) '' Icc a (a + p) = univ :=
eq_top_mono (image_mono Ico_subset_Icc_self) coe_image_Ico_eq _ _

/--
lemma `Ico_ext` / 引理 `Ico_ext`

English:
lemma Ico_ext
  statement: {α : Type*} {f g : AddCircle p -> α} (a : 𝕜)
  proof: by
  rw [← Set.eqOn_univ]; rw [← coe_image_Ico_eq p a]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

中文:
引理 Ico_ext
  结论: {α : 类型} {f g : AddCircle p -> α} (a : 𝕜)
  证明: by
  rw [← Set.eqOn_univ]; rw [← coe_image_Ico_eq p a]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

Depends on / 依赖: Set.eqOn_univ, coe_image_Ico_eq, eqOn_univ
-/
lemma Ico_ext {α : Type*} {f g : AddCircle p -> α} (a : 𝕜)
    (h : forall x in Ico a (a + p), f x = g x) : f = g := by
  rw [← Set.eqOn_univ]; rw [← coe_image_Ico_eq p a]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

/--
lemma `Ioc_ext` / 引理 `Ioc_ext`

English:
lemma Ioc_ext
  statement: {α : Type*} {f g : AddCircle p -> α} (a : 𝕜)
  proof: by
  rw [← Set.eqOn_univ]; rw [← coe_image_Ioc_eq p a]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

中文:
引理 Ioc_ext
  结论: {α : 类型} {f g : AddCircle p -> α} (a : 𝕜)
  证明: by
  rw [← Set.eqOn_univ]; rw [← coe_image_Ioc_eq p a]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

Depends on / 依赖: Set.eqOn_univ, coe_image_Ioc_eq, eqOn_univ
-/
lemma Ioc_ext {α : Type*} {f g : AddCircle p -> α} (a : 𝕜)
    (h : forall x in Ioc a (a + p), f x = g x) : f = g := by
  rw [← Set.eqOn_univ]; rw [← coe_image_Ioc_eq p a]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

end LinearOrderedAddCommGroup

section LinearOrderedField

variable [Field 𝕜] (p q : 𝕜)

/--
Definition of `equivAddCircle` / `equivAddCircle` 的定义

English:
definition equivAddCircle
  signature: (hp : p != 0) (hq : q != 0)
  body: QuotientAddGroup.congr _ _ (AddAut.mulRight <| (Units.mk0 p hp)⁻¹ * Units.mk0 q hq) by
    rw [AddMonoidHom.map_zmultiples]; rw [AddMonoidHom.coe_coe]; rw [AddAut.mulRight_apply]; rw [Units.val_mul]; rw [Units.val_mk0]; rw [Units.val_inv_eq_inv_val]; rw [Units.val_mk0]; rw [mul_inv_cancel_left₀ hp]

@[simp]

中文:
定义 equivAddCircle
  签名: (hp : p != 0) (hq : q != 0)
  定义体: QuotientAddGroup.congr _ _ (AddAut.mulRight <| (Units.mk0 p hp)⁻¹ * Units.mk0 q hq) by
    rw [AddMonoidHom.map_zmultiples]; rw [AddMonoidHom.coe_coe]; rw [AddAut.mulRight_apply]; rw [Units.val_mul]; rw [Units.val_mk0]; rw [Units.val_inv_eq_inv_val]; rw [Units.val_mk0]; rw [mul_inv_cancel_left₀ hp]

@[simp]

Depends on / 依赖: AddAut, AddAut.mulRight, AddAut.mulRight_apply, AddMonoidHom, AddMonoidHom.coe_coe, AddMonoidHom.map_zmultiples, QuotientAddGroup, QuotientAddGroup.congr, Units.mk0, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mul, coe_coe, map_zmultiples, mulRight, mulRight_apply, val_inv_eq_inv_val, val_mk0, val_mul
-/
def equivAddCircle (hp : p != 0) (hq : q != 0) : AddCircle p ≃+ AddCircle q :=
QuotientAddGroup.congr _ _ (AddAut.mulRight <| (Units.mk0 p hp)⁻¹ * Units.mk0 q hq) by
    rw [AddMonoidHom.map_zmultiples]; rw [AddMonoidHom.coe_coe]; rw [AddAut.mulRight_apply]; rw [Units.val_mul]; rw [Units.val_mk0]; rw [Units.val_inv_eq_inv_val]; rw [Units.val_mk0]; rw [mul_inv_cancel_left₀ hp]

@[simp]
/--
theorem `equivAddCircle_apply_mk` / 定理 `equivAddCircle_apply_mk`

English:
theorem equivAddCircle_apply_mk
  given: (hp : p != 0) (hq : q != 0) (x : 𝕜)
  proof: rfl

@[simp]

中文:
定理 equivAddCircle_apply_mk
  条件: (hp : p != 0) (hq : q != 0) (x : 𝕜)
  证明: rfl

@[simp]
-/
theorem equivAddCircle_apply_mk (hp : p != 0) (hq : q != 0) (x : 𝕜) :
    equivAddCircle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
  rfl

@[simp]
/--
theorem `equivAddCircle_symm_apply_mk` / 定理 `equivAddCircle_symm_apply_mk`

English:
theorem equivAddCircle_symm_apply_mk
  given: (hp : p != 0) (hq : q != 0) (x : 𝕜)
  proof: rfl

中文:
定理 equivAddCircle_symm_apply_mk
  条件: (hp : p != 0) (hq : q != 0) (x : 𝕜)
  证明: rfl
-/
theorem equivAddCircle_symm_apply_mk (hp : p != 0) (hq : q != 0) (x : 𝕜) :
    (equivAddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
  rfl

section
variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]

/--
Definition of `homeomorphAddCircle` / `homeomorphAddCircle` 的定义

English:
definition homeomorphAddCircle
  signature: (hp : p != 0) (hq : q != 0)
  body: ⟨equivAddCircle p q hp hq,
    (continuous_quotient_mk'.comp (continuous_mul_const (p⁻¹ * q))).quotient_lift _,
    (continuous_quotient_mk'.comp (continuous_mul_const (q⁻¹ * p))).quotient_lift _⟩

@[simp]

中文:
定义 homeomorphAddCircle
  签名: (hp : p != 0) (hq : q != 0)
  定义体: ⟨equivAddCircle p q hp hq,
    (continuous_quotient_mk'.comp (continuous_mul_const (p⁻¹ * q))).quotient_lift _,
    (continuous_quotient_mk'.comp (continuous_mul_const (q⁻¹ * p))).quotient_lift _⟩

@[simp]

Depends on / 依赖: continuous_mul_const, continuous_quotient_mk, equivAddCircle, quotient_lift
-/
def homeomorphAddCircle (hp : p != 0) (hq : q != 0) : AddCircle p ≃ₜ AddCircle q :=
  ⟨equivAddCircle p q hp hq,
    (continuous_quotient_mk'.comp (continuous_mul_const (p⁻¹ * q))).quotient_lift _,
    (continuous_quotient_mk'.comp (continuous_mul_const (q⁻¹ * p))).quotient_lift _⟩

@[simp]
/--
theorem `homeomorphAddCircle_apply_mk` / 定理 `homeomorphAddCircle_apply_mk`

English:
theorem homeomorphAddCircle_apply_mk
  given: (hp : p != 0) (hq : q != 0) (x : 𝕜)
  proof: rfl

@[simp]

中文:
定理 homeomorphAddCircle_apply_mk
  条件: (hp : p != 0) (hq : q != 0) (x : 𝕜)
  证明: rfl

@[simp]
-/
theorem homeomorphAddCircle_apply_mk (hp : p != 0) (hq : q != 0) (x : 𝕜) :
    homeomorphAddCircle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
  rfl

@[simp]
/--
theorem `homeomorphAddCircle_symm_apply_mk` / 定理 `homeomorphAddCircle_symm_apply_mk`

English:
theorem homeomorphAddCircle_symm_apply_mk
  given: (hp : p != 0) (hq : q != 0) (x : 𝕜)
  proof: rfl

中文:
定理 homeomorphAddCircle_symm_apply_mk
  条件: (hp : p != 0) (hq : q != 0) (x : 𝕜)
  证明: rfl
-/
theorem homeomorphAddCircle_symm_apply_mk (hp : p != 0) (hq : q != 0) (x : 𝕜) :
    (homeomorphAddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
  rfl
end

/--
lemma `natCast_div_mul_eq_nsmul` / 引理 `natCast_div_mul_eq_nsmul`

English:
lemma natCast_div_mul_eq_nsmul
  given: (r : 𝕜) (m : Nat)
  proof: by
  rw [mul_comm_div]; rw [← nsmul_eq_mul]; rw [coe_nsmul]

中文:
引理 natCast_div_mul_eq_nsmul
  条件: (r : 𝕜) (m : 自然数)
  证明: by
  rw [mul_comm_div]; rw [← nsmul_eq_mul]; rw [coe_nsmul]

Depends on / 依赖: coe_nsmul, mul_comm_div, nsmul_eq_mul
-/
lemma natCast_div_mul_eq_nsmul (r : 𝕜) (m : Nat) :
    (↑(↑m / q * r) : AddCircle p) = m • (r / q : AddCircle p) := by
  rw [mul_comm_div]; rw [← nsmul_eq_mul]; rw [coe_nsmul]

/--
lemma `intCast_div_mul_eq_zsmul` / 引理 `intCast_div_mul_eq_zsmul`

English:
lemma intCast_div_mul_eq_zsmul
  given: (r : 𝕜) (m : Int)
  proof: by
  rw [mul_comm_div]; rw [← zsmul_eq_mul]; rw [coe_zsmul]

中文:
引理 intCast_div_mul_eq_zsmul
  条件: (r : 𝕜) (m : 整数)
  证明: by
  rw [mul_comm_div]; rw [← zsmul_eq_mul]; rw [coe_zsmul]

Depends on / 依赖: coe_zsmul, mul_comm_div, zsmul_eq_mul
-/
lemma intCast_div_mul_eq_zsmul (r : 𝕜) (m : Int) :
    (↑(↑m / q * r) : AddCircle p) = m • (r / q : AddCircle p) := by
  rw [mul_comm_div]; rw [← zsmul_eq_mul]; rw [coe_zsmul]

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [hp : Fact (0 < p)]

section FloorRing

variable [FloorRing 𝕜]

@[simp]
/--
theorem `coe_equivIco_mk_apply` / 定理 `coe_equivIco_mk_apply`

English:
theorem coe_equivIco_mk_apply
  given: (x : 𝕜)
  proof: toIcoMod_eq_fract_mul _ x

中文:
定理 coe_equivIco_mk_apply
  条件: (x : 𝕜)
  证明: toIcoMod_eq_fract_mul _ x

Depends on / 依赖: toIcoMod_eq_fract_mul
-/
theorem coe_equivIco_mk_apply (x : 𝕜) :
    (equivIco p 0 <| QuotientAddGroup.mk x : 𝕜) = Int.fract (x / p) * p :=
  toIcoMod_eq_fract_mul _ x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DivisibleBy (AddCircle p) Int
  body: (↑((n : 𝕜)⁻¹ * (equivIco p 0 x : 𝕜)) : AddCircle p)
  div_zero x := by simp
  div_cancel {n} x hn := by
    replace hn : (n : 𝕜) != 0 := by norm_cast
    change n • QuotientAddGroup.mk' _ ((n : 𝕜)⁻¹ * ↑(equivIco p 0 x)) = x
    rw [← map_zsmul]; rw [← smul_mul_assoc]; rw [zsmul_eq_mul]; rw [mul_inv_cancel₀ hn]; rw [one_mul]
    exact (equivIco p 0).symm_apply_apply x

omit [IsStrictOrderedRing 𝕜] in

中文:
实例 :
  签名: DivisibleBy (AddCircle p) 整数
  定义体: (↑((n : 𝕜)⁻¹ * (equivIco p 0 x : 𝕜)) : AddCircle p)
  div_zero x := by simp
  div_cancel {n} x hn := by
    replace hn : (n : 𝕜) != 0 := by norm_cast
    change n • QuotientAddGroup.mk' _ ((n : 𝕜)⁻¹ * ↑(equivIco p 0 x)) = x
    rw [← map_zsmul]; rw [← smul_mul_assoc]; rw [zsmul_eq_mul]; rw [mul_inv_cancel₀ hn]; rw [one_mul]
    exact (equivIco p 0).symm_apply_apply x

omit [IsStrictOrderedRing 𝕜] in

Depends on / 依赖: AddCircle, equivIco
-/
instance : DivisibleBy (AddCircle p) Int where
  div x n := (↑((n : 𝕜)⁻¹ * (equivIco p 0 x : 𝕜)) : AddCircle p)
  div_zero x := by simp
  div_cancel {n} x hn := by
    replace hn : (n : 𝕜) != 0 := by norm_cast
    change n • QuotientAddGroup.mk' _ ((n : 𝕜)⁻¹ * ↑(equivIco p 0 x)) = x
    rw [← map_zsmul]; rw [← smul_mul_assoc]; rw [zsmul_eq_mul]; rw [mul_inv_cancel₀ hn]; rw [one_mul]
    exact (equivIco p 0).symm_apply_apply x

omit [IsStrictOrderedRing 𝕜] in
/--
lemma `coe_fract` / 引理 `coe_fract`

English:
lemma coe_fract
  given: (x : 𝕜)
  statement: (↑(Int.fract x) : AddCircle (1 : 𝕜)) = x
  proof: by
  simp [← Int.self_sub_floor, mem_zmultiples_iff]

中文:
引理 coe_fract
  条件: (x : 𝕜)
  结论: (↑(整数.fract x) : AddCircle (1 : 𝕜)) = x
  证明: by
  simp [← Int.self_sub_floor, mem_zmultiples_iff]
-/
@[simp] lemma coe_fract (x : 𝕜) : (↑(Int.fract x) : AddCircle (1 : 𝕜)) = x := by
  simp [← Int.self_sub_floor, mem_zmultiples_iff]

end FloorRing

section FiniteOrderPoints

variable {p}

/--
theorem `addOrderOf_period_div` / 定理 `addOrderOf_period_div`

English:
theorem addOrderOf_period_div
  given: {n : Nat} (h : 0 < n)
  statement: addOrderOf ((p / n : 𝕜) : AddCircle p) = n
  proof: by
  rw [addOrderOf_eq_iff h]
  replace h : 0 < (n : 𝕜) := Nat.cast_pos.2 h
  refine ⟨?_, fun m hn h0 => ?_⟩ <;> simp only [Ne, ← coe_nsmul, nsmul_eq_mul]
  · rw [mul_div_cancel₀ _ h.ne', coe_period]
  rw [coe_eq_zero_of_pos_iff p hp.out (mul_pos (Nat.cast_pos.2 h0) <| div_pos hp.out h)]
  rintro ⟨k, hk⟩
  rw [mul_div]; rw [eq_div_iff h.ne']; rw [nsmul_eq_mul]; rw [mul_right_comm]; rw [← Nat.cast_mul]; rw [(mul_left_injective₀ hp.out.ne').eq_iff]; rw [Nat.cast_inj]; rw [mul_comm] at hk
  exact (Nat.le_of_dvd h0 ⟨_, hk.symm⟩).not_gt hn

中文:
定理 addOrderOf_period_div
  条件: {n : 自然数} (h : 0 < n)
  结论: addOrderOf ((p / n : 𝕜) : AddCircle p) = n
  证明: by
  rw [addOrderOf_eq_iff h]
  replace h : 0 < (n : 𝕜) := Nat.cast_pos.2 h
  refine ⟨?_, fun m hn h0 => ?_⟩ <;> simp only [Ne, ← coe_nsmul, nsmul_eq_mul]
  · rw [mul_div_cancel₀ _ h.ne', coe_period]
  rw [coe_eq_zero_of_pos_iff p hp.out (mul_pos (Nat.cast_pos.2 h0) <| div_pos hp.out h)]
  rintro ⟨k, hk⟩
  rw [mul_div]; rw [eq_div_iff h.ne']; rw [nsmul_eq_mul]; rw [mul_right_comm]; rw [← Nat.cast_mul]; rw [(mul_left_injective₀ hp.out.ne').eq_iff]; rw [Nat.cast_inj]; rw [mul_comm] at hk
  exact (Nat.le_of_dvd h0 ⟨_, hk.symm⟩).not_gt hn

Depends on / 依赖: Nat.cast_inj, Nat.cast_mul, Nat.cast_pos, Nat.le_of_dvd, addOrderOf_eq_iff, cast_inj, cast_mul, cast_pos, coe_eq_zero_of_pos_iff, coe_nsmul, coe_period, div_pos, eq_div_iff, eq_iff, h.ne, hp.out, hp.out.ne, le_of_dvd, mul_comm, mul_div
-/
theorem addOrderOf_period_div {n : Nat} (h : 0 < n) : addOrderOf ((p / n : 𝕜) : AddCircle p) = n := by
  rw [addOrderOf_eq_iff h]
  replace h : 0 < (n : 𝕜) := Nat.cast_pos.2 h
  refine ⟨?_, fun m hn h0 => ?_⟩ <;> simp only [Ne, ← coe_nsmul, nsmul_eq_mul]
  · rw [mul_div_cancel₀ _ h.ne', coe_period]
  rw [coe_eq_zero_of_pos_iff p hp.out (mul_pos (Nat.cast_pos.2 h0) <| div_pos hp.out h)]
  rintro ⟨k, hk⟩
  rw [mul_div]; rw [eq_div_iff h.ne']; rw [nsmul_eq_mul]; rw [mul_right_comm]; rw [← Nat.cast_mul]; rw [(mul_left_injective₀ hp.out.ne').eq_iff]; rw [Nat.cast_inj]; rw [mul_comm] at hk
  exact (Nat.le_of_dvd h0 ⟨_, hk.symm⟩).not_gt hn

variable (p) in
/--
theorem `gcd_mul_addOrderOf_div_eq` / 定理 `gcd_mul_addOrderOf_div_eq`

English:
theorem gcd_mul_addOrderOf_div_eq
  given: {n : Nat} (m : Nat) (hn : 0 < n)
  proof: by
  rw [natCast_div_mul_eq_nsmul]; rw [IsOfFinAddOrder.addOrderOf_nsmul]
  · rw [addOrderOf_period_div hn, Nat.gcd_comm, Nat.mul_div_cancel']
    exact n.gcd_dvd_left m
  · rwa [← addOrderOf_pos_iff, addOrderOf_period_div hn]

中文:
定理 gcd_mul_addOrderOf_div_eq
  条件: {n : 自然数} (m : 自然数) (hn : 0 < n)
  证明: by
  rw [natCast_div_mul_eq_nsmul]; rw [IsOfFinAddOrder.addOrderOf_nsmul]
  · rw [addOrderOf_period_div hn, Nat.gcd_comm, Nat.mul_div_cancel']
    exact n.gcd_dvd_left m
  · rwa [← addOrderOf_pos_iff, addOrderOf_period_div hn]

Depends on / 依赖: IsOfFinAddOrder, IsOfFinAddOrder.addOrderOf_nsmul, Nat.gcd_comm, Nat.mul_div_cancel, addOrderOf_nsmul, addOrderOf_period_div, addOrderOf_pos_iff, gcd_comm, gcd_dvd_left, mul_div_cancel, n.gcd_dvd_left, natCast_div_mul_eq_nsmul
-/
theorem gcd_mul_addOrderOf_div_eq {n : Nat} (m : Nat) (hn : 0 < n) :
    m.gcd n * addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  rw [natCast_div_mul_eq_nsmul]; rw [IsOfFinAddOrder.addOrderOf_nsmul]
  · rw [addOrderOf_period_div hn, Nat.gcd_comm, Nat.mul_div_cancel']
    exact n.gcd_dvd_left m
  · rwa [← addOrderOf_pos_iff, addOrderOf_period_div hn]

/--
theorem `addOrderOf_div_of_gcd_eq_one` / 定理 `addOrderOf_div_of_gcd_eq_one`

English:
theorem addOrderOf_div_of_gcd_eq_one
  given: {m n : Nat} (hn : 0 < n) (h : m.gcd n = 1)
  proof: by
  convert! gcd_mul_addOrderOf_div_eq p m hn
  rw [h]; rw [one_mul]

中文:
定理 addOrderOf_div_of_gcd_eq_one
  条件: {m n : 自然数} (hn : 0 < n) (h : m.最大公约数 n = 1)
  证明: by
  convert! gcd_mul_addOrderOf_div_eq p m hn
  rw [h]; rw [one_mul]

Depends on / 依赖: convert, gcd_mul_addOrderOf_div_eq, one_mul
-/
theorem addOrderOf_div_of_gcd_eq_one {m n : Nat} (hn : 0 < n) (h : m.gcd n = 1) :
    addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  convert! gcd_mul_addOrderOf_div_eq p m hn
  rw [h]; rw [one_mul]

/--
theorem `addOrderOf_div_of_gcd_eq_one'` / 定理 `addOrderOf_div_of_gcd_eq_one'`

English:
theorem addOrderOf_div_of_gcd_eq_one'
  given: {m : Int} {n : Nat} (hn : 0 < n) (h : m.natAbs.gcd n = 1)
  proof: by
  cases m
  · simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.natAbs_natCast] at h ⊢
    exact addOrderOf_div_of_gcd_eq_one hn h
  · simp only [Int.cast_negSucc, neg_div, neg_mul, coe_neg, addOrderOf_neg]
    exact addOrderOf_div_of_gcd_eq_one hn h

中文:
定理 addOrderOf_div_of_gcd_eq_one'
  条件: {m : 整数} {n : 自然数} (hn : 0 < n) (h : m.natAbs.最大公约数 n = 1)
  证明: by
  cases m
  · simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.natAbs_natCast] at h ⊢
    exact addOrderOf_div_of_gcd_eq_one hn h
  · simp only [Int.cast_negSucc, neg_div, neg_mul, coe_neg, addOrderOf_neg]
    exact addOrderOf_div_of_gcd_eq_one hn h

Depends on / 依赖: Int.cast_natCast, Int.cast_negSucc, Int.natAbs_natCast, Int.ofNat_eq_natCast, addOrderOf_div_of_gcd_eq_one, addOrderOf_neg, cast_natCast, cast_negSucc, coe_neg, natAbs_natCast, neg_div, neg_mul, ofNat_eq_natCast
-/
theorem addOrderOf_div_of_gcd_eq_one' {m : Int} {n : Nat} (hn : 0 < n) (h : m.natAbs.gcd n = 1) :
    addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  cases m
  · simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.natAbs_natCast] at h ⊢
    exact addOrderOf_div_of_gcd_eq_one hn h
  · simp only [Int.cast_negSucc, neg_div, neg_mul, coe_neg, addOrderOf_neg]
    exact addOrderOf_div_of_gcd_eq_one hn h

/--
theorem `addOrderOf_coe_rat` / 定理 `addOrderOf_coe_rat`

English:
theorem addOrderOf_coe_rat
  given: {q : Rat}
  statement: addOrderOf (↑(↑q * p) : AddCircle p) = q.den
  proof: by
  have : (↑(q.den : Int) : 𝕜) != 0 := by
    norm_cast
    exact q.pos.ne.symm
  rw [← q.num_divInt_den]; rw [Rat.cast_divInt_of_ne_zero _ this]; rw [Int.cast_natCast]; rw [Rat.num_divInt_den]; rw [addOrderOf_div_of_gcd_eq_one' q.pos q.reduced]

中文:
定理 addOrderOf_coe_rat
  条件: {q : 有理数}
  结论: addOrderOf (↑(↑q * p) : AddCircle p) = q.den
  证明: by
  have : (↑(q.den : Int) : 𝕜) != 0 := by
    norm_cast
    exact q.pos.ne.symm
  rw [← q.num_divInt_den]; rw [Rat.cast_divInt_of_ne_zero _ this]; rw [Int.cast_natCast]; rw [Rat.num_divInt_den]; rw [addOrderOf_div_of_gcd_eq_one' q.pos q.reduced]

Depends on / 依赖: Int.cast_natCast, Rat.cast_divInt_of_ne_zero, Rat.num_divInt_den, addOrderOf_div_of_gcd_eq_one, cast_divInt_of_ne_zero, cast_natCast, num_divInt_den, q.den, q.num_divInt_den, q.pos, q.pos.ne.symm, q.reduced, reduced
-/
theorem addOrderOf_coe_rat {q : Rat} : addOrderOf (↑(↑q * p) : AddCircle p) = q.den := by
  have : (↑(q.den : Int) : 𝕜) != 0 := by
    norm_cast
    exact q.pos.ne.symm
  rw [← q.num_divInt_den]; rw [Rat.cast_divInt_of_ne_zero _ this]; rw [Int.cast_natCast]; rw [Rat.num_divInt_den]; rw [addOrderOf_div_of_gcd_eq_one' q.pos q.reduced]

/--
theorem `nsmul_eq_zero_iff` / 定理 `nsmul_eq_zero_iff`

English:
theorem nsmul_eq_zero_iff
  given: {u : AddCircle p} {n : Nat} (h : 0 < n)
  proof: by
  refine ⟨QuotientAddGroup.induction_on u fun k hk => ?_, ?_⟩
  · rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
    rintro ⟨m, -, rfl⟩
    constructor; rw [mul_comm, eq_comm]
    exact gcd_mul_addOrderOf_div_eq p m h
  rw [← coe_nsmul]; rw [coe_eq_zero_iff] at hk
  obtain ⟨a, ha⟩ := hk
  refine ⟨a.natMod n, Int.natMod_lt h.ne', ?_⟩
  have h0 : (n : 𝕜) != 0 := Nat.cast_ne_zero.2 h.ne'
  rw [nsmul_eq_mul]; rw [mul_comm]; rw [← div_eq_iff h0]; rw [← a.ediv_mul_add_emod n]; rw [add_smul]; rw [add_div]; rw [zsmul_eq_mul]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [mul_assoc]; rw [← mul_div]; rw [mul_comm _ p]; rw [mul_div_cancel_right₀ p h0] at ha
  rw [← ha]; rw [coe_add]; rw [← Int.cast_natCast]; rw [Int.natMod]; rw [Int.toNat_of_nonneg]; rw [zsmul_eq_mul]; rw [mul_div_right_comm]; rw [eq_comm]; rw [add_eq_right]; rw [← zsmul_eq_mul]; rw [coe_zsmul]; rw [coe_period]; rw [smul_zero]
  exact Int.emod_nonneg _ (by exact_mod_cast h.ne')

中文:
定理 nsmul_eq_zero_iff
  条件: {u : AddCircle p} {n : 自然数} (h : 0 < n)
  证明: by
  refine ⟨QuotientAddGroup.induction_on u fun k hk => ?_, ?_⟩
  · rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
    rintro ⟨m, -, rfl⟩
    constructor; rw [mul_comm, eq_comm]
    exact gcd_mul_addOrderOf_div_eq p m h
  rw [← coe_nsmul]; rw [coe_eq_zero_iff] at hk
  obtain ⟨a, ha⟩ := hk
  refine ⟨a.natMod n, Int.natMod_lt h.ne', ?_⟩
  have h0 : (n : 𝕜) != 0 := Nat.cast_ne_zero.2 h.ne'
  rw [nsmul_eq_mul]; rw [mul_comm]; rw [← div_eq_iff h0]; rw [← a.ediv_mul_add_emod n]; rw [add_smul]; rw [add_div]; rw [zsmul_eq_mul]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [mul_assoc]; rw [← mul_div]; rw [mul_comm _ p]; rw [mul_div_cancel_right₀ p h0] at ha
  rw [← ha]; rw [coe_add]; rw [← Int.cast_natCast]; rw [Int.natMod]; rw [Int.toNat_of_nonneg]; rw [zsmul_eq_mul]; rw [mul_div_right_comm]; rw [eq_comm]; rw [add_eq_right]; rw [← zsmul_eq_mul]; rw [coe_zsmul]; rw [coe_period]; rw [smul_zero]
  exact Int.emod_nonneg _ (by exact_mod_cast h.ne')
-/
protected theorem nsmul_eq_zero_iff {u : AddCircle p} {n : Nat} (h : 0 < n) :
    n • u = 0 ↔ exists m < n, ↑(↑m / ↑n * p) = u := by
  refine ⟨QuotientAddGroup.induction_on u fun k hk => ?_, ?_⟩
  · rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
    rintro ⟨m, -, rfl⟩
    constructor; rw [mul_comm, eq_comm]
    exact gcd_mul_addOrderOf_div_eq p m h
  rw [← coe_nsmul]; rw [coe_eq_zero_iff] at hk
  obtain ⟨a, ha⟩ := hk
  refine ⟨a.natMod n, Int.natMod_lt h.ne', ?_⟩
  have h0 : (n : 𝕜) != 0 := Nat.cast_ne_zero.2 h.ne'
  rw [nsmul_eq_mul]; rw [mul_comm]; rw [← div_eq_iff h0]; rw [← a.ediv_mul_add_emod n]; rw [add_smul]; rw [add_div]; rw [zsmul_eq_mul]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [mul_assoc]; rw [← mul_div]; rw [mul_comm _ p]; rw [mul_div_cancel_right₀ p h0] at ha
  rw [← ha]; rw [coe_add]; rw [← Int.cast_natCast]; rw [Int.natMod]; rw [Int.toNat_of_nonneg]; rw [zsmul_eq_mul]; rw [mul_div_right_comm]; rw [eq_comm]; rw [add_eq_right]; rw [← zsmul_eq_mul]; rw [coe_zsmul]; rw [coe_period]; rw [smul_zero]
  exact Int.emod_nonneg _ (by exact_mod_cast h.ne')

/--
theorem `addOrderOf_eq_pos_iff` / 定理 `addOrderOf_eq_pos_iff`

English:
theorem addOrderOf_eq_pos_iff
  given: {u : AddCircle p} {n : Nat} (h : 0 < n)
  proof: by
  refine ⟨QuotientAddGroup.induction_on u ?_, ?_⟩
  · rintro ⟨m, -, h₁, rfl⟩
    exact addOrderOf_div_of_gcd_eq_one h h₁
  rintro k rfl
  obtain ⟨m, hm, hk⟩ := (AddCircle.nsmul_eq_zero_iff h).mp
    (addOrderOf_nsmul_eq_zero (k : AddCircle p))
  refine ⟨m, hm, mul_right_cancel₀ h.ne' ?_, hk⟩
  convert! gcd_mul_addOrderOf_div_eq p m h using 1
  · rw [hk]
  · apply one_mul

中文:
定理 addOrderOf_eq_pos_iff
  条件: {u : AddCircle p} {n : 自然数} (h : 0 < n)
  证明: by
  refine ⟨QuotientAddGroup.induction_on u ?_, ?_⟩
  · rintro ⟨m, -, h₁, rfl⟩
    exact addOrderOf_div_of_gcd_eq_one h h₁
  rintro k rfl
  obtain ⟨m, hm, hk⟩ := (AddCircle.nsmul_eq_zero_iff h).mp
    (addOrderOf_nsmul_eq_zero (k : AddCircle p))
  refine ⟨m, hm, mul_right_cancel₀ h.ne' ?_, hk⟩
  convert! gcd_mul_addOrderOf_div_eq p m h using 1
  · rw [hk]
  · apply one_mul

Depends on / 依赖: AddCircle, AddCircle.nsmul_eq_zero_iff, QuotientAddGroup, QuotientAddGroup.induction_on, addOrderOf_div_of_gcd_eq_one, addOrderOf_nsmul_eq_zero, convert, gcd_mul_addOrderOf_div_eq, h.ne, induction_on, nsmul_eq_zero_iff, one_mul
-/
theorem addOrderOf_eq_pos_iff {u : AddCircle p} {n : Nat} (h : 0 < n) :
    addOrderOf u = n ↔ exists m < n, m.gcd n = 1 ∧ ↑(↑m / ↑n * p) = u := by
  refine ⟨QuotientAddGroup.induction_on u ?_, ?_⟩
  · rintro ⟨m, -, h₁, rfl⟩
    exact addOrderOf_div_of_gcd_eq_one h h₁
  rintro k rfl
  obtain ⟨m, hm, hk⟩ := (AddCircle.nsmul_eq_zero_iff h).mp
    (addOrderOf_nsmul_eq_zero (k : AddCircle p))
  refine ⟨m, hm, mul_right_cancel₀ h.ne' ?_, hk⟩
  convert! gcd_mul_addOrderOf_div_eq p m h using 1
  · rw [hk]
  · apply one_mul

/--
theorem `exists_gcd_eq_one_of_isOfFinAddOrder` / 定理 `exists_gcd_eq_one_of_isOfFinAddOrder`

English:
theorem exists_gcd_eq_one_of_isOfFinAddOrder
  given: {u : AddCircle p} (h : IsOfFinAddOrder u)
  proof: let ⟨m, hl, hg, he⟩ := (addOrderOf_eq_pos_iff h.addOrderOf_pos).1 rfl
  ⟨m, hg, hl, he⟩

中文:
定理 存在_gcd_eq_one_of_isOfFinAddOrder
  条件: {u : AddCircle p} (h : IsOfFinAddOrder u)
  证明: let ⟨m, hl, hg, he⟩ := (addOrderOf_eq_pos_iff h.addOrderOf_pos).1 rfl
  ⟨m, hg, hl, he⟩

Depends on / 依赖: addOrderOf_eq_pos_iff, addOrderOf_pos, h.addOrderOf_pos
-/
theorem exists_gcd_eq_one_of_isOfFinAddOrder {u : AddCircle p} (h : IsOfFinAddOrder u) :
    exists m : Nat, m.gcd (addOrderOf u) = 1 ∧ m < addOrderOf u ∧ ↑((m : 𝕜) / addOrderOf u * p) = u :=
  let ⟨m, hl, hg, he⟩ := (addOrderOf_eq_pos_iff h.addOrderOf_pos).1 rfl
  ⟨m, hg, hl, he⟩

/--
lemma `not_isOfFinAddOrder_iff_forall_rat_ne_div` / 引理 `not_isOfFinAddOrder_iff_forall_rat_ne_div`

English:
lemma not_isOfFinAddOrder_iff_forall_rat_ne_div
  given: {a : 𝕜}
  proof: by
  simp +contextual [← QuotientAddGroup.mk_zsmul, mul_comm (Int.cast _), mem_zmultiples_iff,
    eq_div_iff (Fact.out : 0 < p).ne', isOfFinAddOrder_iff_zsmul_eq_zero, Rat.forall, div_eq_iff,
    div_mul_eq_mul_div]
  grind

中文:
引理 not_isOfFinAddOrder_iff_对任意_rat_ne_div
  条件: {a : 𝕜}
  证明: by
  simp +contextual [← QuotientAddGroup.mk_zsmul, mul_comm (Int.cast _), mem_zmultiples_iff,
    eq_div_iff (Fact.out : 0 < p).ne', isOfFinAddOrder_iff_zsmul_eq_zero, Rat.forall, div_eq_iff,
    div_mul_eq_mul_div]
  grind

Depends on / 依赖: Fact.out, Int.cast, QuotientAddGroup, QuotientAddGroup.mk_zsmul, Rat.forall, contextual, div_eq_iff, div_mul_eq_mul_div, eq_div_iff, isOfFinAddOrder_iff_zsmul_eq_zero, mem_zmultiples_iff, mk_zsmul, mul_comm
-/
lemma not_isOfFinAddOrder_iff_forall_rat_ne_div {a : 𝕜} :
    ¬ IsOfFinAddOrder (a : AddCircle p) ↔ forall q : Rat, (q : 𝕜) != a / p := by
  simp +contextual [← QuotientAddGroup.mk_zsmul, mul_comm (Int.cast _), mem_zmultiples_iff,
    eq_div_iff (Fact.out : 0 < p).ne', isOfFinAddOrder_iff_zsmul_eq_zero, Rat.forall, div_eq_iff,
    div_mul_eq_mul_div]
  grind

/--
lemma `isOfFinAddOrder_iff_exists_rat_eq_div` / 引理 `isOfFinAddOrder_iff_exists_rat_eq_div`

English:
lemma isOfFinAddOrder_iff_exists_rat_eq_div
  given: {a : 𝕜}
  proof: by
  simpa using not_isOfFinAddOrder_iff_forall_rat_ne_div.not_right

中文:
引理 isOfFinAddOrder_iff_存在_rat_eq_div
  条件: {a : 𝕜}
  证明: by
  simpa using not_isOfFinAddOrder_iff_forall_rat_ne_div.not_right

Depends on / 依赖: not_isOfFinAddOrder_iff_forall_rat_ne_div, not_isOfFinAddOrder_iff_forall_rat_ne_div.not_right, not_right
-/
lemma isOfFinAddOrder_iff_exists_rat_eq_div {a : 𝕜} :
    IsOfFinAddOrder (a : AddCircle p) ↔ exists q : Rat, (q : 𝕜) = a / p := by
  simpa using not_isOfFinAddOrder_iff_forall_rat_ne_div.not_right

variable (p)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `setAddOrderOfEquiv` / `setAddOrderOfEquiv` 的定义

English:
definition setAddOrderOfEquiv
  signature: {n : Nat} (hn : 0 < n)
  body: Equiv.symm
    Equiv.ofBijective (fun m => ⟨↑((m : 𝕜) / n * p), addOrderOf_div_of_gcd_eq_one hn m.prop.2⟩)
      (by
        refine ⟨fun m₁ m₂ h => Subtype.ext ?_, fun u => ?_⟩
        · simp_rw [Subtype.mk_eq_mk, natCast_div_mul_eq_nsmul] at h
          refine nsmul_injOn_Iio_addOrderOf ?_ ?_ h <;> rw [addOrderOf_period_div hn]
          exacts [m₁.2.1, m₂.2.1]
        · obtain ⟨m, hmn, hg, he⟩ := (addOrderOf_eq_pos_iff hn).mp u.2
          exact ⟨⟨m, hmn, hg⟩, Subtype.ext he⟩)

@[simp]

中文:
定义 setAddOrderOfEquiv
  签名: {n : 自然数} (hn : 0 < n)
  定义体: Equiv.symm
    Equiv.ofBijective (fun m => ⟨↑((m : 𝕜) / n * p), addOrderOf_div_of_gcd_eq_one hn m.prop.2⟩)
      (by
        refine ⟨fun m₁ m₂ h => Subtype.ext ?_, fun u => ?_⟩
        · simp_rw [Subtype.mk_eq_mk, natCast_div_mul_eq_nsmul] at h
          refine nsmul_injOn_Iio_addOrderOf ?_ ?_ h <;> rw [addOrderOf_period_div hn]
          exacts [m₁.2.1, m₂.2.1]
        · obtain ⟨m, hmn, hg, he⟩ := (addOrderOf_eq_pos_iff hn).mp u.2
          exact ⟨⟨m, hmn, hg⟩, Subtype.ext he⟩)

@[simp]

Depends on / 依赖: Equiv.ofBijective, Equiv.symm, Subtype, Subtype.ext, Subtype.mk_eq_mk, addOrderOf_div_of_gcd_eq_one, addOrderOf_eq_pos_iff, addOrderOf_period_div, exacts, m.prop, mk_eq_mk, natCast_div_mul_eq_nsmul, nsmul_injOn_Iio_addOrderOf, ofBijective, simp_rw
-/
def setAddOrderOfEquiv {n : Nat} (hn : 0 < n) :
    { u : AddCircle p | addOrderOf u = n } ≃ { m | m < n ∧ m.gcd n = 1 } :=
Equiv.symm
    Equiv.ofBijective (fun m => ⟨↑((m : 𝕜) / n * p), addOrderOf_div_of_gcd_eq_one hn m.prop.2⟩)
      (by
        refine ⟨fun m₁ m₂ h => Subtype.ext ?_, fun u => ?_⟩
        · simp_rw [Subtype.mk_eq_mk, natCast_div_mul_eq_nsmul] at h
          refine nsmul_injOn_Iio_addOrderOf ?_ ?_ h <;> rw [addOrderOf_period_div hn]
          exacts [m₁.2.1, m₂.2.1]
        · obtain ⟨m, hmn, hg, he⟩ := (addOrderOf_eq_pos_iff hn).mp u.2
          exact ⟨⟨m, hmn, hg⟩, Subtype.ext he⟩)

@[simp]
/--
theorem `card_addOrderOf_eq_totient` / 定理 `card_addOrderOf_eq_totient`

English:
theorem card_addOrderOf_eq_totient
  given: {n : Nat}
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp only [Nat.totient_zero, addOrderOf_eq_zero_iff]
    rcases em (exists u : AddCircle p, ¬IsOfFinAddOrder u) with (⟨u, hu⟩ | h)
    · have : Infinite { u : AddCircle p // ¬IsOfFinAddOrder u } := by
        rw [← coe_ofPred]; rw [infinite_coe_iff]
        exact infinite_not_isOfFinAddOrder hu
      exact Nat.card_eq_zero_of_infinite
    · have : IsEmpty { u : AddCircle p // ¬IsOfFinAddOrder u } := by simpa [isEmpty_subtype] using h
      exact Nat.card_of_isEmpty
  · rw [← coe_ofPred, Nat.card_congr (setAddOrderOfEquiv p hn),
      n.totient_eq_card_lt_and_coprime]
    simp only [Nat.gcd_comm]

中文:
定理 card_addOrderOf_eq_totient
  条件: {n : 自然数}
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp only [Nat.totient_zero, addOrderOf_eq_zero_iff]
    rcases em (exists u : AddCircle p, ¬IsOfFinAddOrder u) with (⟨u, hu⟩ | h)
    · have : Infinite { u : AddCircle p // ¬IsOfFinAddOrder u } := by
        rw [← coe_ofPred]; rw [infinite_coe_iff]
        exact infinite_not_isOfFinAddOrder hu
      exact Nat.card_eq_zero_of_infinite
    · have : IsEmpty { u : AddCircle p // ¬IsOfFinAddOrder u } := by simpa [isEmpty_subtype] using h
      exact Nat.card_of_isEmpty
  · rw [← coe_ofPred, Nat.card_congr (setAddOrderOfEquiv p hn),
      n.totient_eq_card_lt_and_coprime]
    simp only [Nat.gcd_comm]

Depends on / 依赖: AddCircle, Infinite, IsEmpty, IsOfFinAddOrder, Nat.c, Nat.card_eq_zero_of_infinite, Nat.card_of_isEmpty, Nat.totient_zero, addOrderOf_eq_zero_iff, card_eq_zero_of_infinite, card_of_isEmpty, coe_ofPred, eq_zero_or_pos, infinite_coe_iff, infinite_not_isOfFinAddOrder, isEmpty_subtype, n.eq_zero_or_pos, totient_zero
-/
theorem card_addOrderOf_eq_totient {n : Nat} :
    Nat.card { u : AddCircle p // addOrderOf u = n } = n.totient := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp only [Nat.totient_zero, addOrderOf_eq_zero_iff]
    rcases em (exists u : AddCircle p, ¬IsOfFinAddOrder u) with (⟨u, hu⟩ | h)
    · have : Infinite { u : AddCircle p // ¬IsOfFinAddOrder u } := by
        rw [← coe_ofPred]; rw [infinite_coe_iff]
        exact infinite_not_isOfFinAddOrder hu
      exact Nat.card_eq_zero_of_infinite
    · have : IsEmpty { u : AddCircle p // ¬IsOfFinAddOrder u } := by simpa [isEmpty_subtype] using h
      exact Nat.card_of_isEmpty
  · rw [← coe_ofPred, Nat.card_congr (setAddOrderOfEquiv p hn),
      n.totient_eq_card_lt_and_coprime]
    simp only [Nat.gcd_comm]

end FiniteOrderPoints

end LinearOrderedField

end AddCircle

section IdentifyIccEnds

/-! This section proves that for any `a`, the natural map from `[a, a + p] ⊂ 𝕜` to `AddCircle p`
gives an identification of `AddCircle p`, as a topological space, with the quotient of `[a, a + p]`
by the equivalence relation identifying the endpoints. -/

namespace AddCircle

variable [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] (p a : 𝕜)
  [hp : Fact (0 < p)]

local notation "𝕋" => AddCircle p

/--
Inductive type `EndpointIdent` / 归纳类型 `EndpointIdent`

English:
inductive EndpointIdent
  parameters: : Icc a (a + p) -> Icc a (a + p) -> Prop
  constructors (1):
    - mk: 

中文:
归纳类型 EndpointIdent
  参数: : 闭区间 a (a + p) -> 闭区间 a (a + p) -> 命题
  构造子 (1 个):
    - mk: 
-/
inductive EndpointIdent : Icc a (a + p) -> Icc a (a + p) -> Prop
  | mk :
EndpointIdent ⟨a, left_mem_Icc.mpr le_add_of_nonneg_right hp.out.le⟩
⟨a + p, right_mem_Icc.mpr le_add_of_nonneg_right hp.out.le⟩

variable [Archimedean 𝕜]

/--
Definition of `equivIccQuot` / `equivIccQuot` 的定义

English:
definition equivIccQuot
  signature: : 𝕋 ≃ Quot (EndpointIdent p a) where
  body: Quot.mk _ inclusion Ico_subset_Icc_self (equivIco _ _ x)
  invFun x :=
Quot.liftOn x (↑) by
      rintro _ _ ⟨_⟩
      exact (coe_add_period p a).symm
  left_inv := (equivIco p a).symm_apply_apply
  right_inv :=
Quot.ind by
      rintro ⟨x, hx⟩
      rcases ne_or_eq x (a + p) with (h | rfl)
      · revert x
        dsimp only
        intro x hx h
        congr
        ext1
        apply congr_arg Subtype.val ((equivIco p a).right_inv ⟨x, hx.1, hx.2.lt_of_ne h⟩)
      · rw [← Quot.sound EndpointIdent.mk]
        dsimp only
        congr
        ext1
        apply congr_arg Subtype.val
          ((equivIco p a).right_inv ⟨a, le_refl a, lt_add_of_pos_right a hp.out⟩)

中文:
定义 equivIccQuot
  签名: : 𝕋 ≃ 商 (EndpointIdent p a) where
  定义体: Quot.mk _ inclusion Ico_subset_Icc_self (equivIco _ _ x)
  invFun x :=
Quot.liftOn x (↑) by
      rintro _ _ ⟨_⟩
      exact (coe_add_period p a).symm
  left_inv := (equivIco p a).symm_apply_apply
  right_inv :=
Quot.ind by
      rintro ⟨x, hx⟩
      rcases ne_or_eq x (a + p) with (h | rfl)
      · revert x
        dsimp only
        intro x hx h
        congr
        ext1
        apply congr_arg Subtype.val ((equivIco p a).right_inv ⟨x, hx.1, hx.2.lt_of_ne h⟩)
      · rw [← Quot.sound EndpointIdent.mk]
        dsimp only
        congr
        ext1
        apply congr_arg Subtype.val
          ((equivIco p a).right_inv ⟨a, le_refl a, lt_add_of_pos_right a hp.out⟩)

Depends on / 依赖: Ico_subset_Icc_self, Quot.mk, equivIco, inclusion
-/
def equivIccQuot : 𝕋 ≃ Quot (EndpointIdent p a) where
toFun x := Quot.mk _ inclusion Ico_subset_Icc_self (equivIco _ _ x)
  invFun x :=
Quot.liftOn x (↑) by
      rintro _ _ ⟨_⟩
      exact (coe_add_period p a).symm
  left_inv := (equivIco p a).symm_apply_apply
  right_inv :=
Quot.ind by
      rintro ⟨x, hx⟩
      rcases ne_or_eq x (a + p) with (h | rfl)
      · revert x
        dsimp only
        intro x hx h
        congr
        ext1
        apply congr_arg Subtype.val ((equivIco p a).right_inv ⟨x, hx.1, hx.2.lt_of_ne h⟩)
      · rw [← Quot.sound EndpointIdent.mk]
        dsimp only
        congr
        ext1
        apply congr_arg Subtype.val
          ((equivIco p a).right_inv ⟨a, le_refl a, lt_add_of_pos_right a hp.out⟩)

/--
theorem `equivIccQuot_comp_mk_eq_toIcoMod` / 定理 `equivIccQuot_comp_mk_eq_toIcoMod`

English:
theorem equivIccQuot_comp_mk_eq_toIcoMod
  proof: rfl

中文:
定理 equivIccQuot_comp_mk_eq_toIcoMod
  证明: rfl
-/
theorem equivIccQuot_comp_mk_eq_toIcoMod :
    equivIccQuot p a ∘ Quotient.mk'' = fun x =>
Quot.mk _ ⟨toIcoMod hp.out a x, Ico_subset_Icc_self toIcoMod_mem_Ico _ _ x⟩ :=
  rfl

/--
theorem `equivIccQuot_comp_mk_eq_toIocMod` / 定理 `equivIccQuot_comp_mk_eq_toIocMod`

English:
theorem equivIccQuot_comp_mk_eq_toIocMod
  proof: by
  rw [equivIccQuot_comp_mk_eq_toIcoMod]
  funext x
  by_cases h : a ≡ x [PMOD p]
  · simp_rw [(modEq_iff_toIcoMod_eq_left hp.out).1 h, (modEq_iff_toIocMod_eq_right hp.out).1 h]
    exact Quot.sound EndpointIdent.mk
  · simp_rw [(not_modEq_iff_toIcoMod_eq_toIocMod hp.out).1 h]

中文:
定理 equivIccQuot_comp_mk_eq_toIocMod
  证明: by
  rw [equivIccQuot_comp_mk_eq_toIcoMod]
  funext x
  by_cases h : a ≡ x [PMOD p]
  · simp_rw [(modEq_iff_toIcoMod_eq_left hp.out).1 h, (modEq_iff_toIocMod_eq_right hp.out).1 h]
    exact Quot.sound EndpointIdent.mk
  · simp_rw [(not_modEq_iff_toIcoMod_eq_toIocMod hp.out).1 h]

Depends on / 依赖: EndpointIdent, EndpointIdent.mk, Quot.sound, equivIccQuot_comp_mk_eq_toIcoMod, hp.out, modEq_iff_toIcoMod_eq_left, modEq_iff_toIocMod_eq_right, not_modEq_iff_toIcoMod_eq_toIocMod, simp_rw
-/
theorem equivIccQuot_comp_mk_eq_toIocMod :
    equivIccQuot p a ∘ Quotient.mk'' = fun x =>
Quot.mk _ ⟨toIocMod hp.out a x, Ioc_subset_Icc_self toIocMod_mem_Ioc _ _ x⟩ := by
  rw [equivIccQuot_comp_mk_eq_toIcoMod]
  funext x
  by_cases h : a ≡ x [PMOD p]
  · simp_rw [(modEq_iff_toIcoMod_eq_left hp.out).1 h, (modEq_iff_toIocMod_eq_right hp.out).1 h]
    exact Quot.sound EndpointIdent.mk
  · simp_rw [(not_modEq_iff_toIcoMod_eq_toIocMod hp.out).1 h]

/--
Definition of `homeoIccQuot` / `homeoIccQuot` 的定义

English:
definition homeoIccQuot
  signature: [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  body: equivIccQuot p a
  continuous_toFun := by
    simp_rw [isQuotientMap_quotient_mk'.continuous_iff, continuous_iff_continuousAt,
      continuousAt_iff_continuous_left_right]
    intro x; constructor
    on_goal 1 => erw [equivIccQuot_comp_mk_eq_toIocMod]
    on_goal 2 => erw [equivIccQuot_comp_mk_eq_toIcoMod]
    all_goals
      apply continuous_quot_mk.continuousAt.comp_continuousWithinAt
      rw [IsInducing.subtypeVal.continuousWithinAt_iff]
    · apply continuousWithinAt_toIocMod_Iic
    · apply continuousWithinAt_toIcoMod_Ici
  continuous_invFun :=
    continuous_quot_lift _ ((AddCircle.continuous_mk' p).comp continuous_subtype_val)

中文:
定义 homeoIccQuot
  签名: [拓扑空间 𝕜] [Order拓扑 𝕜]
  定义体: equivIccQuot p a
  continuous_toFun := by
    simp_rw [isQuotientMap_quotient_mk'.continuous_iff, continuous_iff_continuousAt,
      continuousAt_iff_continuous_left_right]
    intro x; constructor
    on_goal 1 => erw [equivIccQuot_comp_mk_eq_toIocMod]
    on_goal 2 => erw [equivIccQuot_comp_mk_eq_toIcoMod]
    all_goals
      apply continuous_quot_mk.continuousAt.comp_continuousWithinAt
      rw [IsInducing.subtypeVal.continuousWithinAt_iff]
    · apply continuousWithinAt_toIocMod_Iic
    · apply continuousWithinAt_toIcoMod_Ici
  continuous_invFun :=
    continuous_quot_lift _ ((AddCircle.continuous_mk' p).comp continuous_subtype_val)

Depends on / 依赖: equivIccQuot
-/
def homeoIccQuot [TopologicalSpace 𝕜] [OrderTopology 𝕜] : 𝕋 ≃ₜ Quot (EndpointIdent p a) where
  toEquiv := equivIccQuot p a
  continuous_toFun := by
    simp_rw [isQuotientMap_quotient_mk'.continuous_iff, continuous_iff_continuousAt,
      continuousAt_iff_continuous_left_right]
    intro x; constructor
    on_goal 1 => erw [equivIccQuot_comp_mk_eq_toIocMod]
    on_goal 2 => erw [equivIccQuot_comp_mk_eq_toIcoMod]
    all_goals
      apply continuous_quot_mk.continuousAt.comp_continuousWithinAt
      rw [IsInducing.subtypeVal.continuousWithinAt_iff]
    · apply continuousWithinAt_toIocMod_Iic
    · apply continuousWithinAt_toIcoMod_Ici
  continuous_invFun :=
    continuous_quot_lift _ ((AddCircle.continuous_mk' p).comp continuous_subtype_val)

/-! We now show that a continuous function on `[a, a + p]` satisfying `f a = f (a + p)` is the
pullback of a continuous function on `AddCircle p`, by first showing that
various lifts are equivalent. -/


variable {p a}

/--
theorem `liftIoc_eq_liftIco` / 定理 `liftIoc_eq_liftIco`

English:
theorem liftIoc_eq_liftIco
  given: {f : 𝕜 -> B} (hf : f a = f (a + p))
  proof: by
  ext q
  obtain ⟨x, hx, rfl⟩ := by simpa only [mem_image] using coe_image_Ico_eq p a ▸ mem_univ q
  rw [liftIco_coe_apply hx]
  obtain (⟨rfl, -⟩ | h) := by rwa [mem_Ico, le_iff_eq_or_lt, or_and_right] at hx
  · rw [← coe_add_period, liftIoc_coe_apply (by simp [hp.out]), hf]
  · exact liftIoc_coe_apply ⟨h.1, h.2.le⟩

中文:
定理 liftIoc_eq_liftIco
  条件: {f : 𝕜 -> B} (hf : f a = f (a + p))
  证明: by
  ext q
  obtain ⟨x, hx, rfl⟩ := by simpa only [mem_image] using coe_image_Ico_eq p a ▸ mem_univ q
  rw [liftIco_coe_apply hx]
  obtain (⟨rfl, -⟩ | h) := by rwa [mem_Ico, le_iff_eq_or_lt, or_and_right] at hx
  · rw [← coe_add_period, liftIoc_coe_apply (by simp [hp.out]), hf]
  · exact liftIoc_coe_apply ⟨h.1, h.2.le⟩

Depends on / 依赖: coe_add_period, coe_image_Ico_eq, hp.out, le_iff_eq_or_lt, liftIco_coe_apply, liftIoc_coe_apply, mem_Ico, mem_image, mem_univ, or_and_right
-/
theorem liftIoc_eq_liftIco {f : 𝕜 -> B} (hf : f a = f (a + p)) :
    liftIoc p a f = liftIco p a f := by
  ext q
  obtain ⟨x, hx, rfl⟩ := by simpa only [mem_image] using coe_image_Ico_eq p a ▸ mem_univ q
  rw [liftIco_coe_apply hx]
  obtain (⟨rfl, -⟩ | h) := by rwa [mem_Ico, le_iff_eq_or_lt, or_and_right] at hx
  · rw [← coe_add_period, liftIoc_coe_apply (by simp [hp.out]), hf]
  · exact liftIoc_coe_apply ⟨h.1, h.2.le⟩

/--
theorem `liftIco_eq_lift_Icc` / 定理 `liftIco_eq_lift_Icc`

English:
theorem liftIco_eq_lift_Icc
  given: {f : 𝕜 -> B} (h : f a = f (a + p))
  proof: rfl

中文:
定理 liftIco_eq_lift_Icc
  条件: {f : 𝕜 -> B} (h : f a = f (a + p))
  证明: rfl
-/
theorem liftIco_eq_lift_Icc {f : 𝕜 -> B} (h : f a = f (a + p)) :
    liftIco p a f =
      Quot.lift (domRestrict (Icc a <| a + p) f)
          (by
            rintro _ _ ⟨_⟩
            exact h) ∘
        equivIccQuot p a :=
  rfl

/--
theorem `liftIoc_eq_lift_Icc` / 定理 `liftIoc_eq_lift_Icc`

English:
theorem liftIoc_eq_lift_Icc
  given: {f : 𝕜 -> B} (h : f a = f (a + p))
  proof: by
  rw [← liftIco_eq_lift_Icc h]
  exact liftIoc_eq_liftIco h

中文:
定理 liftIoc_eq_lift_Icc
  条件: {f : 𝕜 -> B} (h : f a = f (a + p))
  证明: by
  rw [← liftIco_eq_lift_Icc h]
  exact liftIoc_eq_liftIco h

Depends on / 依赖: liftIco_eq_lift_Icc, liftIoc_eq_liftIco
-/
theorem liftIoc_eq_lift_Icc {f : 𝕜 -> B} (h : f a = f (a + p)) :
    liftIoc p a f =
      Quot.lift (domRestrict (Icc a <| a + p) f)
          (by
            rintro _ _ ⟨_⟩
            exact h) ∘
        equivIccQuot p a := by
  rw [← liftIco_eq_lift_Icc h]
  exact liftIoc_eq_liftIco h

/--
theorem `liftIco_zero_coe_apply` / 定理 `liftIco_zero_coe_apply`

English:
theorem liftIco_zero_coe_apply
  given: {f : 𝕜 -> B} {x : 𝕜} (hx : x in Ico 0 p)
  statement: liftIco p 0 f ↑x = f x
  proof: liftIco_coe_apply (by rwa [zero_add])

中文:
定理 liftIco_zero_coe_apply
  条件: {f : 𝕜 -> B} {x : 𝕜} (hx : x in 左闭右开区间 0 p)
  结论: liftIco p 0 f ↑x = f x
  证明: liftIco_coe_apply (by rwa [zero_add])

Depends on / 依赖: liftIco_coe_apply, zero_add
-/
theorem liftIco_zero_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx : x in Ico 0 p) : liftIco p 0 f ↑x = f x :=
  liftIco_coe_apply (by rwa [zero_add])

/--
theorem `liftIoc_zero_coe_apply` / 定理 `liftIoc_zero_coe_apply`

English:
theorem liftIoc_zero_coe_apply
  given: {f : 𝕜 -> B} {x : 𝕜} (hx : x in Ioc 0 p)
  statement: liftIoc p 0 f ↑x = f x
  proof: liftIoc_coe_apply (by rwa [zero_add])

中文:
定理 liftIoc_zero_coe_apply
  条件: {f : 𝕜 -> B} {x : 𝕜} (hx : x in 左开右闭区间 0 p)
  结论: liftIoc p 0 f ↑x = f x
  证明: liftIoc_coe_apply (by rwa [zero_add])

Depends on / 依赖: liftIoc_coe_apply, zero_add
-/
theorem liftIoc_zero_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx : x in Ioc 0 p) : liftIoc p 0 f ↑x = f x :=
  liftIoc_coe_apply (by rwa [zero_add])

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

/--
theorem `liftIco_continuous` / 定理 `liftIco_continuous`

English:
theorem liftIco_continuous
  statement: [TopologicalSpace B] {f : 𝕜 -> B} (hf : f a = f (a + p))
  proof: by
  rw [liftIco_eq_lift_Icc hf]
  refine Continuous.comp ?_ (homeoIccQuot p a).continuous_toFun
  exact continuous_coinduced_dom.mpr (continuousOn_iff_continuous_domRestrict.mp hc)

中文:
定理 liftIco_continuous
  结论: [拓扑空间 B] {f : 𝕜 -> B} (hf : f a = f (a + p))
  证明: by
  rw [liftIco_eq_lift_Icc hf]
  refine Continuous.comp ?_ (homeoIccQuot p a).continuous_toFun
  exact continuous_coinduced_dom.mpr (continuousOn_iff_continuous_domRestrict.mp hc)

Depends on / 依赖: Continuous, Continuous.comp, continuousOn_iff_continuous_domRestrict, continuousOn_iff_continuous_domRestrict.mp, continuous_coinduced_dom, continuous_coinduced_dom.mpr, continuous_toFun, homeoIccQuot, liftIco_eq_lift_Icc
-/
theorem liftIco_continuous [TopologicalSpace B] {f : 𝕜 -> B} (hf : f a = f (a + p))
    (hc : ContinuousOn f <| Icc a (a + p)) : Continuous (liftIco p a f) := by
  rw [liftIco_eq_lift_Icc hf]
  refine Continuous.comp ?_ (homeoIccQuot p a).continuous_toFun
  exact continuous_coinduced_dom.mpr (continuousOn_iff_continuous_domRestrict.mp hc)

/--
theorem `liftIco_zero_continuous` / 定理 `liftIco_zero_continuous`

English:
theorem liftIco_zero_continuous
  statement: [TopologicalSpace B] {f : 𝕜 -> B} (hf : f 0 = f p)
  proof: liftIco_continuous (by rwa [zero_add] : f 0 = f (0 + p)) (by rwa [zero_add])

中文:
定理 liftIco_zero_continuous
  结论: [拓扑空间 B] {f : 𝕜 -> B} (hf : f 0 = f p)
  证明: liftIco_continuous (by rwa [zero_add] : f 0 = f (0 + p)) (by rwa [zero_add])

Depends on / 依赖: liftIco_continuous, zero_add
-/
theorem liftIco_zero_continuous [TopologicalSpace B] {f : 𝕜 -> B} (hf : f 0 = f p)
    (hc : ContinuousOn f <| Icc 0 p) : Continuous (liftIco p 0 f) :=
  liftIco_continuous (by rwa [zero_add] : f 0 = f (0 + p)) (by rwa [zero_add])

/--
theorem `liftIoc_continuous` / 定理 `liftIoc_continuous`

English:
theorem liftIoc_continuous
  statement: [TopologicalSpace B] {f : 𝕜 -> B} (hf : f a = f (a + p))
  proof: by
  rw [liftIoc_eq_lift_Icc hf]
  refine Continuous.comp ?_ (homeoIccQuot p a).continuous_toFun
  exact continuous_coinduced_dom.mpr (continuousOn_iff_continuous_domRestrict.mp hc)

中文:
定理 liftIoc_continuous
  结论: [拓扑空间 B] {f : 𝕜 -> B} (hf : f a = f (a + p))
  证明: by
  rw [liftIoc_eq_lift_Icc hf]
  refine Continuous.comp ?_ (homeoIccQuot p a).continuous_toFun
  exact continuous_coinduced_dom.mpr (continuousOn_iff_continuous_domRestrict.mp hc)

Depends on / 依赖: Continuous, Continuous.comp, continuousOn_iff_continuous_domRestrict, continuousOn_iff_continuous_domRestrict.mp, continuous_coinduced_dom, continuous_coinduced_dom.mpr, continuous_toFun, homeoIccQuot, liftIoc_eq_lift_Icc
-/
theorem liftIoc_continuous [TopologicalSpace B] {f : 𝕜 -> B} (hf : f a = f (a + p))
    (hc : ContinuousOn f <| Icc a (a + p)) : Continuous (liftIoc p a f) := by
  rw [liftIoc_eq_lift_Icc hf]
  refine Continuous.comp ?_ (homeoIccQuot p a).continuous_toFun
  exact continuous_coinduced_dom.mpr (continuousOn_iff_continuous_domRestrict.mp hc)

/--
theorem `liftIoc_zero_continuous` / 定理 `liftIoc_zero_continuous`

English:
theorem liftIoc_zero_continuous
  statement: [TopologicalSpace B] {f : 𝕜 -> B} (hf : f 0 = f p)
  proof: liftIoc_continuous (by rwa [zero_add] : f 0 = f (0 + p)) (by rwa [zero_add])

中文:
定理 liftIoc_zero_continuous
  结论: [拓扑空间 B] {f : 𝕜 -> B} (hf : f 0 = f p)
  证明: liftIoc_continuous (by rwa [zero_add] : f 0 = f (0 + p)) (by rwa [zero_add])

Depends on / 依赖: liftIoc_continuous, zero_add
-/
theorem liftIoc_zero_continuous [TopologicalSpace B] {f : 𝕜 -> B} (hf : f 0 = f p)
    (hc : ContinuousOn f <| Icc 0 p) : Continuous (liftIoc p 0 f) :=
  liftIoc_continuous (by rwa [zero_add] : f 0 = f (0 + p)) (by rwa [zero_add])

end AddCircle

end IdentifyIccEnds
