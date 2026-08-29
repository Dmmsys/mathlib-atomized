/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Measures positive on nonempty opens

In this file we define a typeclass for measures that are positive on nonempty opens, see
`MeasureTheory.Measure.IsOpenPosMeasure`. Examples include (additive) Haar measures, as well as
measures that have positive density with respect to a Haar measure. We also prove some basic facts
about these measures.

-/

public section


open Topology ENNReal MeasureTheory

open Set Function Filter

namespace MeasureTheory

namespace Measure

section Basic

variable {X Y : Type*} [TopologicalSpace X] {m : MeasurableSpace X} [TopologicalSpace Y]
  [T2Space Y] (μ ν : Measure X)

/--
Definition of `IsOpenPosMeasure` / `IsOpenPosMeasure` 的定义

English:
class IsOpenPosMeasure
  parameters: : Prop where
  axioms and operations (1):
    - open_pos : forall U : Set X, IsOpen U -> U.Nonempty -> μ U != 0

中文:
类 是OpenPosMeasure
  参数: : 命题 where
  公理与运算 (1 个):
    - open_pos : 对任意 U : 集合 X, 是开集 U -> U.非空 -> μ U != 0
-/
class IsOpenPosMeasure : Prop where
  open_pos : forall U : Set X, IsOpen U -> U.Nonempty -> μ U != 0

variable [IsOpenPosMeasure μ] {s U F : Set X} {x : X}

/--
theorem `_root_.IsOpen.measure_ne_zero` / 定理 `_root_.IsOpen.measure_ne_zero`

English:
theorem _root_.IsOpen.measure_ne_zero
  given: (hU : IsOpen U) (hne : U.Nonempty)
  statement: μ U != 0
  proof: IsOpenPosMeasure.open_pos U hU hne

中文:
定理 _root_.是开集.measure_ne_zero
  条件: (hU : 是开集 U) (hne : U.非空)
  结论: μ U != 0
  证明: IsOpenPosMeasure.open_pos U hU hne

Depends on / 依赖: IsOpenPosMeasure, IsOpenPosMeasure.open_pos, open_pos
-/
theorem _root_.IsOpen.measure_ne_zero (hU : IsOpen U) (hne : U.Nonempty) : μ U != 0 :=
  IsOpenPosMeasure.open_pos U hU hne

/--
theorem `_root_.IsOpen.measure_pos` / 定理 `_root_.IsOpen.measure_pos`

English:
theorem _root_.IsOpen.measure_pos
  given: (hU : IsOpen U) (hne : U.Nonempty)
  statement: 0 < μ U
  proof: (hU.measure_ne_zero μ hne).bot_lt

中文:
定理 _root_.是开集.measure_pos
  条件: (hU : 是开集 U) (hne : U.非空)
  结论: 0 < μ U
  证明: (hU.measure_ne_zero μ hne).bot_lt

Depends on / 依赖: bot_lt, hU.measure_ne_zero, measure_ne_zero
-/
theorem _root_.IsOpen.measure_pos (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U :=
  (hU.measure_ne_zero μ hne).bot_lt

instance (priority := 100) [Nonempty X] : NeZero μ :=
⟨measure_univ_pos.mp isOpen_univ.measure_pos μ univ_nonempty⟩

/--
theorem `_root_.IsOpen.measure_pos_iff` / 定理 `_root_.IsOpen.measure_pos_iff`

English:
theorem _root_.IsOpen.measure_pos_iff
  given: (hU : IsOpen U)
  statement: 0 < μ U ↔ U.Nonempty
  proof: ⟨fun h => nonempty_iff_ne_empty.2 fun he => h.ne' he.symm ▸ measure_empty, hU.measure_pos μ⟩

中文:
定理 _root_.是开集.measure_pos_iff
  条件: (hU : 是开集 U)
  结论: 0 < μ U ↔ U.非空
  证明: ⟨fun h => nonempty_iff_ne_empty.2 fun he => h.ne' he.symm ▸ measure_empty, hU.measure_pos μ⟩

Depends on / 依赖: h.ne, hU.measure_pos, he.symm, measure_empty, measure_pos, nonempty_iff_ne_empty
-/
theorem _root_.IsOpen.measure_pos_iff (hU : IsOpen U) : 0 < μ U ↔ U.Nonempty :=
⟨fun h => nonempty_iff_ne_empty.2 fun he => h.ne' he.symm ▸ measure_empty, hU.measure_pos μ⟩

/--
theorem `_root_.IsOpen.measure_eq_zero_iff` / 定理 `_root_.IsOpen.measure_eq_zero_iff`

English:
theorem _root_.IsOpen.measure_eq_zero_iff
  given: (hU : IsOpen U)
  statement: μ U = 0 ↔ U = ∅
  proof: by
  simpa only [not_lt, nonpos_iff_eq_zero, not_nonempty_iff_eq_empty] using
    not_congr (hU.measure_pos_iff μ)

中文:
定理 _root_.是开集.measure_eq_zero_iff
  条件: (hU : 是开集 U)
  结论: μ U = 0 ↔ U = ∅
  证明: by
  simpa only [not_lt, nonpos_iff_eq_zero, not_nonempty_iff_eq_empty] using
    not_congr (hU.measure_pos_iff μ)

Depends on / 依赖: BooleanAlgebra, BooleanAlgebra.toComplementedLattice, ComplementedLattice, hU.measure_pos_iff, measure_pos_iff, nonpos_iff_eq_zero, not_congr, not_lt, not_nonempty_iff_eq_empty, toComplementedLattice
-/
theorem _root_.IsOpen.measure_eq_zero_iff (hU : IsOpen U) : μ U = 0 ↔ U = ∅ := by
  simpa only [not_lt, nonpos_iff_eq_zero, not_nonempty_iff_eq_empty] using
    not_congr (hU.measure_pos_iff μ)

/--
theorem `measure_pos_of_nonempty_interior` / 定理 `measure_pos_of_nonempty_interior`

English:
theorem measure_pos_of_nonempty_interior
  given: (h : (interior s).Nonempty)
  statement: 0 < μ s
  proof: (isOpen_interior.measure_pos μ h).trans_le (measure_mono interior_subset)

中文:
定理 measure_pos_of_nonempty_interior
  条件: (h : (interior s).非空)
  结论: 0 < μ s
  证明: (isOpen_interior.measure_pos μ h).trans_le (measure_mono interior_subset)

Depends on / 依赖: BooleanAlgebra, BooleanAlgebra.toGeneralizedBooleanAlgebra, interior_subset, isOpen_interior, isOpen_interior.measure_pos, measure_mono, measure_pos, toGeneralizedBooleanAlgebra, trans_le
-/
theorem measure_pos_of_nonempty_interior (h : (interior s).Nonempty) : 0 < μ s :=
  (isOpen_interior.measure_pos μ h).trans_le (measure_mono interior_subset)

/--
theorem `measure_pos_of_mem_nhds` / 定理 `measure_pos_of_mem_nhds`

English:
theorem measure_pos_of_mem_nhds
  given: (h : s in 𝓝 x)
  statement: 0 < μ s
  proof: measure_pos_of_nonempty_interior _ ⟨x, mem_interior_iff_mem_nhds.2 h⟩

中文:
定理 measure_pos_of_mem_nhds
  条件: (h : s in 𝓝 x)
  结论: 0 < μ s
  证明: measure_pos_of_nonempty_interior _ ⟨x, mem_interior_iff_mem_nhds.2 h⟩

Depends on / 依赖: BiheytingAlgebra, BooleanAlgebra, BooleanAlgebra.toBiheytingAlgebra, measure_pos_of_nonempty_interior, mem_interior_iff_mem_nhds, toBiheytingAlgebra
-/
theorem measure_pos_of_mem_nhds (h : s in 𝓝 x) : 0 < μ s :=
  measure_pos_of_nonempty_interior _ ⟨x, mem_interior_iff_mem_nhds.2 h⟩

/--
theorem `isOpenPosMeasure_smul` / 定理 `isOpenPosMeasure_smul`

English:
theorem isOpenPosMeasure_smul
  given: {c : Real>=0∞} (h : c != 0)
  statement: IsOpenPosMeasure (c • μ)
  proof: ⟨fun _U Uo Une => mul_ne_zero h (Uo.measure_ne_zero μ Une)⟩

中文:
定理 isOpenPosMeasure_smul
  条件: {c : 实数>=0∞} (h : c != 0)
  结论: 是OpenPosMeasure (c • μ)
  证明: ⟨fun _U Uo Une => mul_ne_zero h (Uo.measure_ne_zero μ Une)⟩

Depends on / 依赖: Uo.measure_ne_zero, measure_ne_zero, mul_ne_zero
-/
theorem isOpenPosMeasure_smul {c : Real>=0∞} (h : c != 0) : IsOpenPosMeasure (c • μ) :=
  ⟨fun _U Uo Une => mul_ne_zero h (Uo.measure_ne_zero μ Une)⟩

variable {μ ν}

/--
theorem `AbsolutelyContinuous.isOpenPosMeasure` / 定理 `AbsolutelyContinuous.isOpenPosMeasure`

English:
theorem AbsolutelyContinuous.isOpenPosMeasure
  given: (h : μ ≪ ν)
  statement: IsOpenPosMeasure ν
  proof: ⟨fun _U ho hne h₀ => ho.measure_ne_zero μ hne (h h₀)⟩

中文:
定理 AbsolutelyContinuous.isOpenPosMeasure
  条件: (h : μ ≪ ν)
  结论: 是OpenPosMeasure ν
  证明: ⟨fun _U ho hne h₀ => ho.measure_ne_zero μ hne (h h₀)⟩
-/
protected theorem AbsolutelyContinuous.isOpenPosMeasure (h : μ ≪ ν) : IsOpenPosMeasure ν :=
  ⟨fun _U ho hne h₀ => ho.measure_ne_zero μ hne (h h₀)⟩

/--
theorem `_root_.LE.le.isOpenPosMeasure` / 定理 `_root_.LE.le.isOpenPosMeasure`

English:
theorem _root_.LE.le.isOpenPosMeasure
  given: (h : μ <= ν)
  statement: IsOpenPosMeasure ν
  proof: h.absolutelyContinuous.isOpenPosMeasure

中文:
定理 _root_.LE.le.isOpenPosMeasure
  条件: (h : μ <= ν)
  结论: 是OpenPosMeasure ν
  证明: h.absolutelyContinuous.isOpenPosMeasure

Depends on / 依赖: absolutelyContinuous, h.absolutelyContinuous.isOpenPosMeasure, isOpenPosMeasure
-/
theorem _root_.LE.le.isOpenPosMeasure (h : μ <= ν) : IsOpenPosMeasure ν :=
  h.absolutelyContinuous.isOpenPosMeasure

/--
theorem `_root_.IsOpen.measure_zero_iff_eq_empty` / 定理 `_root_.IsOpen.measure_zero_iff_eq_empty`

English:
theorem _root_.IsOpen.measure_zero_iff_eq_empty
  given: (hU : IsOpen U)
  proof: ⟨fun h => (hU.measure_eq_zero_iff μ).mp h, fun h => by simp [h]⟩

中文:
定理 _root_.是开集.measure_zero_iff_eq_empty
  条件: (hU : 是开集 U)
  证明: ⟨fun h => (hU.measure_eq_zero_iff μ).mp h, fun h => by simp [h]⟩

Depends on / 依赖: hU.measure_eq_zero_iff, measure_eq_zero_iff
-/
theorem _root_.IsOpen.measure_zero_iff_eq_empty (hU : IsOpen U) :
    μ U = 0 ↔ U = ∅ :=
  ⟨fun h => (hU.measure_eq_zero_iff μ).mp h, fun h => by simp [h]⟩

/--
theorem `_root_.IsOpen.ae_eq_empty_iff_eq` / 定理 `_root_.IsOpen.ae_eq_empty_iff_eq`

English:
theorem _root_.IsOpen.ae_eq_empty_iff_eq
  given: (hU : IsOpen U)
  proof: by
  rw [ae_eq_empty]; rw [hU.measure_zero_iff_eq_empty]

中文:
定理 _root_.是开集.ae_eq_empty_iff_eq
  条件: (hU : 是开集 U)
  证明: by
  rw [ae_eq_empty]; rw [hU.measure_zero_iff_eq_empty]

Depends on / 依赖: ae_eq_empty, hU.measure_zero_iff_eq_empty, measure_zero_iff_eq_empty
-/
theorem _root_.IsOpen.ae_eq_empty_iff_eq (hU : IsOpen U) :
    U =ᵐ[μ] (∅ : Set X) ↔ U = ∅ := by
  rw [ae_eq_empty]; rw [hU.measure_zero_iff_eq_empty]

/--
theorem `_root_.IsOpen.eq_empty_of_measure_zero` / 定理 `_root_.IsOpen.eq_empty_of_measure_zero`

English:
theorem _root_.IsOpen.eq_empty_of_measure_zero
  given: (hU : IsOpen U) (h₀ : μ U = 0)
  statement: U = ∅
  proof: (hU.measure_eq_zero_iff μ).mp h₀

中文:
定理 _root_.是开集.eq_empty_of_measure_zero
  条件: (hU : 是开集 U) (h₀ : μ U = 0)
  结论: U = ∅
  证明: (hU.measure_eq_zero_iff μ).mp h₀

Depends on / 依赖: hU.measure_eq_zero_iff, measure_eq_zero_iff
-/
theorem _root_.IsOpen.eq_empty_of_measure_zero (hU : IsOpen U) (h₀ : μ U = 0) : U = ∅ :=
  (hU.measure_eq_zero_iff μ).mp h₀

set_option backward.isDefEq.respectTransparency false in
/--
theorem `_root_.IsClosed.ae_eq_univ_iff_eq` / 定理 `_root_.IsClosed.ae_eq_univ_iff_eq`

English:
theorem _root_.IsClosed.ae_eq_univ_iff_eq
  given: (hF : IsClosed F)
  proof: by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rwa [ae_eq_univ, hF.isOpen_compl.measure_eq_zero_iff μ, compl_empty_iff] at h

中文:
定理 _root_.是闭集.ae_eq_univ_iff_eq
  条件: (hF : 是闭集 F)
  证明: by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rwa [ae_eq_univ, hF.isOpen_compl.measure_eq_zero_iff μ, compl_empty_iff] at h

Depends on / 依赖: ae_eq_univ, compl_empty_iff, hF.isOpen_compl.measure_eq_zero_iff, isOpen_compl, measure_eq_zero_iff
-/
theorem _root_.IsClosed.ae_eq_univ_iff_eq (hF : IsClosed F) :
    F =ᵐ[μ] univ ↔ F = univ := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rwa [ae_eq_univ, hF.isOpen_compl.measure_eq_zero_iff μ, compl_empty_iff] at h

/--
theorem `_root_.IsClosed.measure_eq_univ_iff_eq` / 定理 `_root_.IsClosed.measure_eq_univ_iff_eq`

English:
theorem _root_.IsClosed.measure_eq_univ_iff_eq
  statement: [OpensMeasurableSpace X] [IsFiniteMeasure μ]
  proof: by
  rw [← ae_eq_univ_iff_measure_eq hF.measurableSet.nullMeasurableSet]; rw [hF.ae_eq_univ_iff_eq]

中文:
定理 _root_.是闭集.measure_eq_univ_iff_eq
  结论: [OpensMeasurable空间 X] [是有限测度 μ]
  证明: by
  rw [← ae_eq_univ_iff_measure_eq hF.measurableSet.nullMeasurableSet]; rw [hF.ae_eq_univ_iff_eq]

Depends on / 依赖: ae_eq_univ_iff_eq, ae_eq_univ_iff_measure_eq, hF.ae_eq_univ_iff_eq, hF.measurableSet.nullMeasurableSet, measurableSet, nullMeasurableSet
-/
theorem _root_.IsClosed.measure_eq_univ_iff_eq [OpensMeasurableSpace X] [IsFiniteMeasure μ]
    (hF : IsClosed F) :
    μ F = μ univ ↔ F = univ := by
  rw [← ae_eq_univ_iff_measure_eq hF.measurableSet.nullMeasurableSet]; rw [hF.ae_eq_univ_iff_eq]

/--
theorem `_root_.IsClosed.measure_eq_one_iff_eq_univ` / 定理 `_root_.IsClosed.measure_eq_one_iff_eq_univ`

English:
theorem _root_.IsClosed.measure_eq_one_iff_eq_univ
  statement: [OpensMeasurableSpace X] [IsProbabilityMeasure μ]
  proof: by
  rw [← measure_univ (μ := μ)]; rw [hF.measure_eq_univ_iff_eq]

中文:
定理 _root_.是闭集.measure_eq_one_iff_eq_univ
  结论: [OpensMeasurable空间 X] [是概率测度 μ]
  证明: by
  rw [← measure_univ (μ := μ)]; rw [hF.measure_eq_univ_iff_eq]

Depends on / 依赖: hF.measure_eq_univ_iff_eq, measure_eq_univ_iff_eq, measure_univ
-/
theorem _root_.IsClosed.measure_eq_one_iff_eq_univ [OpensMeasurableSpace X] [IsProbabilityMeasure μ]
    (hF : IsClosed F) :
    μ F = 1 ↔ F = univ := by
  rw [← measure_univ (μ := μ)]; rw [hF.measure_eq_univ_iff_eq]

/--
theorem `interior_eq_empty_of_null` / 定理 `interior_eq_empty_of_null`

English:
theorem interior_eq_empty_of_null
  given: (hs : μ s = 0)
  statement: interior s = ∅
  proof: isOpen_interior.eq_empty_of_measure_zero measure_mono_null interior_subset hs

中文:
定理 interior_eq_empty_of_null
  条件: (hs : μ s = 0)
  结论: interior s = ∅
  证明: isOpen_interior.eq_empty_of_measure_zero measure_mono_null interior_subset hs

Depends on / 依赖: eq_empty_of_measure_zero, interior_subset, isOpen_interior, isOpen_interior.eq_empty_of_measure_zero, measure_mono_null
-/
theorem interior_eq_empty_of_null (hs : μ s = 0) : interior s = ∅ :=
isOpen_interior.eq_empty_of_measure_zero measure_mono_null interior_subset hs

/--
theorem `dense_of_ae` / 定理 `dense_of_ae`

English:
theorem dense_of_ae
  given: {p : X -> Prop} (hp : forallᵐ x ∂μ, p x)
  statement: Dense {x | p x}
  proof: by
  rw [dense_iff_closure_eq]; rw [closure_eq_compl_interior_compl]; rw [compl_univ_iff]
  exact μ.interior_eq_empty_of_null hp

中文:
定理 dense_of_ae
  条件: {p : X -> 命题} (hp : 对任意ᵐ x ∂μ, p x)
  结论: 稠密 {x | p x}
  证明: by
  rw [dense_iff_closure_eq]; rw [closure_eq_compl_interior_compl]; rw [compl_univ_iff]
  exact μ.interior_eq_empty_of_null hp

Depends on / 依赖: closure_eq_compl_interior_compl, compl_univ_iff, dense_iff_closure_eq, interior_eq_empty_of_null
-/
theorem dense_of_ae {p : X -> Prop} (hp : forallᵐ x ∂μ, p x) : Dense {x | p x} := by
  rw [dense_iff_closure_eq]; rw [closure_eq_compl_interior_compl]; rw [compl_univ_iff]
  exact μ.interior_eq_empty_of_null hp

/--
theorem `eqOn_open_of_ae_eq` / 定理 `eqOn_open_of_ae_eq`

English:
theorem eqOn_open_of_ae_eq
  statement: {f g : X -> Y} (h : f =ᵐ[μ.restrict U] g) (hU : IsOpen U)
  proof: by
  replace h := ae_imp_of_ae_restrict h
  simp only [ae_iff, Classical.not_imp] at h
  have : IsOpen (U inter { a | f a != g a }) := by
    refine isOpen_iff_mem_nhds.mpr fun a ha => inter_mem (hU.mem_nhds ha.1) ?_
    rcases ha with ⟨ha : a in U, ha' : (f a, g a) in (diagonal Y)ᶜ⟩
    exact
     

中文:
定理 eqOn_open_of_ae_eq
  结论: {f g : X -> Y} (h : f =ᵐ[μ.restrict U] g) (hU : 是开集 U)
  证明: by
  replace h := ae_imp_of_ae_restrict h
  simp only [ae_iff, Classical.not_imp] at h
  have : IsOpen (U inter { a | f a != g a }) := by
    refine isOpen_iff_mem_nhds.mpr fun a ha => inter_mem (hU.mem_nhds ha.1) ?_
    rcases ha with ⟨ha : a in U, ha' : (f a, g a) in (diagonal Y)ᶜ⟩
    exact
     

Depends on / 依赖: Classical, Classical.not_imp, Classical.not_not, IsOpen, ae_iff, ae_imp_of_ae_restrict, continuousAt, diagonal, eq_empty_of_measure_zero, hU.mem_nhds, hf.continuousAt, hg.continuousAt, inter_mem, isClosed_diagonal, isClosed_diagonal.isOpen_compl.mem_nhds, isOpen_compl, isOpen_iff_mem_nhds, isOpen_iff_mem_nhds.mpr, mem_nhds, not_imp
-/
theorem eqOn_open_of_ae_eq {f g : X -> Y} (h : f =ᵐ[μ.restrict U] g) (hU : IsOpen U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) : EqOn f g U := by
  replace h := ae_imp_of_ae_restrict h
  simp only [ae_iff, Classical.not_imp] at h
  have : IsOpen (U inter { a | f a != g a }) := by
    refine isOpen_iff_mem_nhds.mpr fun a ha => inter_mem (hU.mem_nhds ha.1) ?_
    rcases ha with ⟨ha : a in U, ha' : (f a, g a) in (diagonal Y)ᶜ⟩
    exact
      (hf.continuousAt (hU.mem_nhds ha)).prodMk_nhds (hg.continuousAt (hU.mem_nhds ha))
        (isClosed_diagonal.isOpen_compl.mem_nhds ha')
  replace := (this.eq_empty_of_measure_zero h).le
  exact fun x hx => Classical.not_not.1 fun h => this ⟨hx, h⟩

/--
theorem `eq_of_ae_eq` / 定理 `eq_of_ae_eq`

English:
theorem eq_of_ae_eq
  given: {f g : X -> Y} (h : f =ᵐ[μ] g) (hf : Continuous f) (hg : Continuous g)
  statement: f = g
  proof: suffices EqOn f g univ from funext fun _ => this trivial
  eqOn_open_of_ae_eq (ae_restrict_of_ae h) isOpen_univ hf.continuousOn hg.continuousOn

中文:
定理 eq_of_ae_eq
  条件: {f g : X -> Y} (h : f =ᵐ[μ] g) (hf : 连续 f) (hg : 连续 g)
  结论: f = g
  证明: suffices EqOn f g univ from funext fun _ => this trivial
  eqOn_open_of_ae_eq (ae_restrict_of_ae h) isOpen_univ hf.continuousOn hg.continuousOn

Depends on / 依赖: ae_restrict_of_ae, continuousOn, eqOn_open_of_ae_eq, hf.continuousOn, hg.continuousOn, isOpen_univ
-/
theorem eq_of_ae_eq {f g : X -> Y} (h : f =ᵐ[μ] g) (hf : Continuous f) (hg : Continuous g) : f = g :=
  suffices EqOn f g univ from funext fun _ => this trivial
  eqOn_open_of_ae_eq (ae_restrict_of_ae h) isOpen_univ hf.continuousOn hg.continuousOn

/--
theorem `eqOn_of_ae_eq` / 定理 `eqOn_of_ae_eq`

English:
theorem eqOn_of_ae_eq
  statement: {f g : X -> Y} (h : f =ᵐ[μ.restrict s] g) (hf : ContinuousOn f s)
  proof: have : interior s subseteq s := interior_subset
  (eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset this h) isOpen_interior (hf.mono this)
        (hg.mono this)).of_subset_closure
    hf hg this hU

中文:
定理 eqOn_of_ae_eq
  结论: {f g : X -> Y} (h : f =ᵐ[μ.restrict s] g) (hf : ContinuousOn f s)
  证明: have : interior s subseteq s := interior_subset
  (eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset this h) isOpen_interior (hf.mono this)
        (hg.mono this)).of_subset_closure
    hf hg this hU

Depends on / 依赖: ae_restrict_of_ae_restrict_of_subset, eqOn_open_of_ae_eq, hf.mono, hg.mono, interior, interior_subset, isOpen_interior, of_subset_closure, subseteq
-/
theorem eqOn_of_ae_eq {f g : X -> Y} (h : f =ᵐ[μ.restrict s] g) (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) (hU : s subseteq closure (interior s)) : EqOn f g s :=
  have : interior s subseteq s := interior_subset
  (eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset this h) isOpen_interior (hf.mono this)
        (hg.mono this)).of_subset_closure
    hf hg this hU

variable (μ) in
/--
theorem `_root_.Continuous.ae_eq_iff_eq` / 定理 `_root_.Continuous.ae_eq_iff_eq`

English:
theorem _root_.Continuous.ae_eq_iff_eq
  given: {f g : X -> Y} (hf : Continuous f) (hg : Continuous g)
  proof: ⟨fun h => eq_of_ae_eq h hf hg, fun h => h ▸ EventuallyEq.rfl⟩

中文:
定理 _root_.连续.ae_eq_iff_eq
  条件: {f g : X -> Y} (hf : 连续 f) (hg : 连续 g)
  证明: ⟨fun h => eq_of_ae_eq h hf hg, fun h => h ▸ EventuallyEq.rfl⟩

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, eq_of_ae_eq
-/
theorem _root_.Continuous.ae_eq_iff_eq {f g : X -> Y} (hf : Continuous f) (hg : Continuous g) :
    f =ᵐ[μ] g ↔ f = g :=
  ⟨fun h => eq_of_ae_eq h hf hg, fun h => h ▸ EventuallyEq.rfl⟩

/--
theorem `_root_.Continuous.isOpenPosMeasure_map` / 定理 `_root_.Continuous.isOpenPosMeasure_map`

English:
theorem _root_.Continuous.isOpenPosMeasure_map
  statement: [OpensMeasurableSpace X]
  proof: by
  refine ⟨fun U hUo hUne => ?_⟩
  rw [Measure.map_apply hf.measurable hUo.measurableSet]
  exact (hUo.preimage hf).measure_ne_zero μ (hf_surj.nonempty_preimage.mpr hUne)

中文:
定理 _root_.连续.isOpenPosMeasure_map
  结论: [OpensMeasurable空间 X]
  证明: by
  refine ⟨fun U hUo hUne => ?_⟩
  rw [Measure.map_apply hf.measurable hUo.measurableSet]
  exact (hUo.preimage hf).measure_ne_zero μ (hf_surj.nonempty_preimage.mpr hUne)

Depends on / 依赖: Measure, Measure.map_apply, hUo.measurableSet, hUo.preimage, hf.measurable, hf_surj, hf_surj.nonempty_preimage.mpr, map_apply, measurable, measurableSet, measure_ne_zero, nonempty_preimage, preimage
-/
theorem _root_.Continuous.isOpenPosMeasure_map [OpensMeasurableSpace X]
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {f : X -> Z} (hf : Continuous f) (hf_surj : Function.Surjective f) :
    (Measure.map f μ).IsOpenPosMeasure := by
  refine ⟨fun U hUo hUne => ?_⟩
  rw [Measure.map_apply hf.measurable hUo.measurableSet]
  exact (hUo.preimage hf).measure_ne_zero μ (hf_surj.nonempty_preimage.mpr hUne)

/--
theorem `IsOpenPosMeasure.comap` / 定理 `IsOpenPosMeasure.comap`

English:
theorem IsOpenPosMeasure.comap
  statement: [BorelSpace X]
  proof: by
    rw [hf.measurableEmbedding.comap_apply]
    exact IsOpenPosMeasure.open_pos _ (hf.isOpen_iff_image_isOpen.mp hU) (Une.image f)

中文:
定理 是OpenPosMeasure.comap
  结论: [Borel空间 X]
  证明: by
    rw [hf.measurableEmbedding.comap_apply]
    exact IsOpenPosMeasure.open_pos _ (hf.isOpen_iff_image_isOpen.mp hU) (Une.image f)
-/
protected theorem IsOpenPosMeasure.comap [BorelSpace X]
    {Z : Type*} [TopologicalSpace Z] {mZ : MeasurableSpace Z} [BorelSpace Z]
    (μ : Measure Z) [IsOpenPosMeasure μ] {f : X -> Z} (hf : IsOpenEmbedding f) :
    (μ.comap f).IsOpenPosMeasure where
  open_pos U hU Une := by
    rw [hf.measurableEmbedding.comap_apply]
    exact IsOpenPosMeasure.open_pos _ (hf.isOpen_iff_image_isOpen.mp hU) (Une.image f)

end Basic

section LinearOrder

variable {X Y : Type*} [TopologicalSpace X] [LinearOrder X] [OrderTopology X]
  {m : MeasurableSpace X} [TopologicalSpace Y] [T2Space Y] (μ : Measure X) [IsOpenPosMeasure μ]

/--
theorem `measure_Ioi_pos` / 定理 `measure_Ioi_pos`

English:
theorem measure_Ioi_pos
  given: [NoMaxOrder X] (a : X)
  statement: 0 < μ (Ioi a)
  proof: isOpen_Ioi.measure_pos μ nonempty_Ioi

中文:
定理 measure_Ioi_pos
  条件: [NoMax序 X] (a : X)
  结论: 0 < μ (左开右无界区间 a)
  证明: isOpen_Ioi.measure_pos μ nonempty_Ioi

Depends on / 依赖: isOpen_Ioi, isOpen_Ioi.measure_pos, measure_pos, nonempty_Ioi
-/
theorem measure_Ioi_pos [NoMaxOrder X] (a : X) : 0 < μ (Ioi a) :=
  isOpen_Ioi.measure_pos μ nonempty_Ioi

/--
theorem `measure_Iio_pos` / 定理 `measure_Iio_pos`

English:
theorem measure_Iio_pos
  given: [NoMinOrder X] (a : X)
  statement: 0 < μ (Iio a)
  proof: isOpen_Iio.measure_pos μ nonempty_Iio

中文:
定理 measure_Iio_pos
  条件: [NoMin序 X] (a : X)
  结论: 0 < μ (左无界右开区间 a)
  证明: isOpen_Iio.measure_pos μ nonempty_Iio

Depends on / 依赖: isOpen_Iio, isOpen_Iio.measure_pos, measure_pos, nonempty_Iio
-/
theorem measure_Iio_pos [NoMinOrder X] (a : X) : 0 < μ (Iio a) :=
  isOpen_Iio.measure_pos μ nonempty_Iio

/--
theorem `measure_Ioo_pos` / 定理 `measure_Ioo_pos`

English:
theorem measure_Ioo_pos
  given: [DenselyOrdered X] {a b : X}
  statement: 0 < μ (Ioo a b) ↔ a < b
  proof: (isOpen_Ioo.measure_pos_iff μ).trans nonempty_Ioo

中文:
定理 measure_Ioo_pos
  条件: [稠密序 X] {a b : X}
  结论: 0 < μ (开区间 a b) ↔ a < b
  证明: (isOpen_Ioo.measure_pos_iff μ).trans nonempty_Ioo

Depends on / 依赖: isOpen_Ioo, isOpen_Ioo.measure_pos_iff, measure_pos_iff, nonempty_Ioo
-/
theorem measure_Ioo_pos [DenselyOrdered X] {a b : X} : 0 < μ (Ioo a b) ↔ a < b :=
  (isOpen_Ioo.measure_pos_iff μ).trans nonempty_Ioo

/--
theorem `measure_Ioo_eq_zero` / 定理 `measure_Ioo_eq_zero`

English:
theorem measure_Ioo_eq_zero
  given: [DenselyOrdered X] {a b : X}
  statement: μ (Ioo a b) = 0 ↔ b <= a
  proof: (isOpen_Ioo.measure_eq_zero_iff μ).trans (Ioo_eq_empty_iff.trans not_lt)

中文:
定理 measure_Ioo_eq_zero
  条件: [稠密序 X] {a b : X}
  结论: μ (开区间 a b) = 0 ↔ b <= a
  证明: (isOpen_Ioo.measure_eq_zero_iff μ).trans (Ioo_eq_empty_iff.trans not_lt)

Depends on / 依赖: Ioo_eq_empty_iff, Ioo_eq_empty_iff.trans, isOpen_Ioo, isOpen_Ioo.measure_eq_zero_iff, measure_eq_zero_iff, not_lt
-/
theorem measure_Ioo_eq_zero [DenselyOrdered X] {a b : X} : μ (Ioo a b) = 0 ↔ b <= a :=
  (isOpen_Ioo.measure_eq_zero_iff μ).trans (Ioo_eq_empty_iff.trans not_lt)

/--
theorem `eqOn_Ioo_of_ae_eq` / 定理 `eqOn_Ioo_of_ae_eq`

English:
theorem eqOn_Ioo_of_ae_eq
  statement: {a b : X} {f g : X -> Y} (hfg : f =ᵐ[μ.restrict (Ioo a b)] g)
  proof: eqOn_of_ae_eq hfg hf hg Ioo_subset_closure_interior

中文:
定理 eqOn_Ioo_of_ae_eq
  结论: {a b : X} {f g : X -> Y} (hfg : f =ᵐ[μ.restrict (开区间 a b)] g)
  证明: eqOn_of_ae_eq hfg hf hg Ioo_subset_closure_interior

Depends on / 依赖: Ioo_subset_closure_interior, eqOn_of_ae_eq
-/
theorem eqOn_Ioo_of_ae_eq {a b : X} {f g : X -> Y} (hfg : f =ᵐ[μ.restrict (Ioo a b)] g)
    (hf : ContinuousOn f (Ioo a b)) (hg : ContinuousOn g (Ioo a b)) : EqOn f g (Ioo a b) :=
  eqOn_of_ae_eq hfg hf hg Ioo_subset_closure_interior

/--
theorem `eqOn_Ioc_of_ae_eq` / 定理 `eqOn_Ioc_of_ae_eq`

English:
theorem eqOn_Ioc_of_ae_eq
  statement: [DenselyOrdered X] {a b : X} {f g : X -> Y}
  proof: eqOn_of_ae_eq hfg hf hg (Ioc_subset_closure_interior _ _)

中文:
定理 eqOn_Ioc_of_ae_eq
  结论: [稠密序 X] {a b : X} {f g : X -> Y}
  证明: eqOn_of_ae_eq hfg hf hg (Ioc_subset_closure_interior _ _)

Depends on / 依赖: Ioc_subset_closure_interior, eqOn_of_ae_eq
-/
theorem eqOn_Ioc_of_ae_eq [DenselyOrdered X] {a b : X} {f g : X -> Y}
    (hfg : f =ᵐ[μ.restrict (Ioc a b)] g) (hf : ContinuousOn f (Ioc a b))
    (hg : ContinuousOn g (Ioc a b)) : EqOn f g (Ioc a b) :=
  eqOn_of_ae_eq hfg hf hg (Ioc_subset_closure_interior _ _)

/--
theorem `eqOn_Ico_of_ae_eq` / 定理 `eqOn_Ico_of_ae_eq`

English:
theorem eqOn_Ico_of_ae_eq
  statement: [DenselyOrdered X] {a b : X} {f g : X -> Y}
  proof: eqOn_of_ae_eq hfg hf hg (Ico_subset_closure_interior _ _)

中文:
定理 eqOn_Ico_of_ae_eq
  结论: [稠密序 X] {a b : X} {f g : X -> Y}
  证明: eqOn_of_ae_eq hfg hf hg (Ico_subset_closure_interior _ _)

Depends on / 依赖: Ico_subset_closure_interior, eqOn_of_ae_eq
-/
theorem eqOn_Ico_of_ae_eq [DenselyOrdered X] {a b : X} {f g : X -> Y}
    (hfg : f =ᵐ[μ.restrict (Ico a b)] g) (hf : ContinuousOn f (Ico a b))
    (hg : ContinuousOn g (Ico a b)) : EqOn f g (Ico a b) :=
  eqOn_of_ae_eq hfg hf hg (Ico_subset_closure_interior _ _)

/--
theorem `eqOn_Icc_of_ae_eq` / 定理 `eqOn_Icc_of_ae_eq`

English:
theorem eqOn_Icc_of_ae_eq
  statement: [DenselyOrdered X] {a b : X} (hne : a != b) {f g : X -> Y}
  proof: eqOn_of_ae_eq hfg hf hg (closure_interior_Icc hne).symm.subset

中文:
定理 eqOn_Icc_of_ae_eq
  结论: [稠密序 X] {a b : X} (hne : a != b) {f g : X -> Y}
  证明: eqOn_of_ae_eq hfg hf hg (closure_interior_Icc hne).symm.subset

Depends on / 依赖: closure_interior_Icc, eqOn_of_ae_eq, subset, symm.subset
-/
theorem eqOn_Icc_of_ae_eq [DenselyOrdered X] {a b : X} (hne : a != b) {f g : X -> Y}
    (hfg : f =ᵐ[μ.restrict (Icc a b)] g) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) : EqOn f g (Icc a b) :=
  eqOn_of_ae_eq hfg hf hg (closure_interior_Icc hne).symm.subset

end LinearOrder

end Measure

end MeasureTheory

open MeasureTheory MeasureTheory.Measure

namespace Metric

variable {X : Type*} [PseudoMetricSpace X] {m : MeasurableSpace X} (μ : Measure X)
  [IsOpenPosMeasure μ]

/--
theorem `measure_ball_pos` / 定理 `measure_ball_pos`

English:
theorem measure_ball_pos
  given: (x : X) {r : Real} (hr : 0 < r)
  statement: 0 < μ (ball x r)
  proof: isOpen_ball.measure_pos μ (nonempty_ball.2 hr)

中文:
定理 measure_ball_pos
  条件: (x : X) {r : 实数} (hr : 0 < r)
  结论: 0 < μ (ball x r)
  证明: isOpen_ball.measure_pos μ (nonempty_ball.2 hr)

Depends on / 依赖: isOpen_ball, isOpen_ball.measure_pos, measure_pos, nonempty_ball
-/
theorem measure_ball_pos (x : X) {r : Real} (hr : 0 < r) : 0 < μ (ball x r) :=
  isOpen_ball.measure_pos μ (nonempty_ball.2 hr)

/--
theorem `measure_closedBall_pos` / 定理 `measure_closedBall_pos`

English:
theorem measure_closedBall_pos
  given: (x : X) {r : Real} (hr : 0 < r)
  statement: 0 < μ (closedBall x r)
  proof: (measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closedBall)

中文:
定理 measure_closedBall_pos
  条件: (x : X) {r : 实数} (hr : 0 < r)
  结论: 0 < μ (closedBall x r)
  证明: (measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closedBall)

Depends on / 依赖: ball_subset_closedBall, measure_ball_pos, measure_mono, trans_le
-/
theorem measure_closedBall_pos (x : X) {r : Real} (hr : 0 < r) : 0 < μ (closedBall x r) :=
  (measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closedBall)

/--
lemma `measure_closedBall_pos_iff` / 引理 `measure_closedBall_pos_iff`

English:
lemma measure_closedBall_pos_iff
  statement: {X : Type*} [MetricSpace X] {m : MeasurableSpace X}
  proof: by
  refine ⟨fun h => ?_, measure_closedBall_pos μ x⟩
  contrapose! h
  rw [(subsingleton_closedBall x h).measure_zero μ]

中文:
引理 measure_closedBall_pos_iff
  结论: {X : 类型} [度量空间 X] {m : 可测空间 X}
  证明: by
  refine ⟨fun h => ?_, measure_closedBall_pos μ x⟩
  contrapose! h
  rw [(subsingleton_closedBall x h).measure_zero μ]
-/
@[simp] lemma measure_closedBall_pos_iff {X : Type*} [MetricSpace X] {m : MeasurableSpace X}
    (μ : Measure X) [IsOpenPosMeasure μ] [NullSingletonClass μ] {x : X} {r : Real} :
    0 < μ (closedBall x r) ↔ 0 < r := by
  refine ⟨fun h => ?_, measure_closedBall_pos μ x⟩
  contrapose! h
  rw [(subsingleton_closedBall x h).measure_zero μ]

end Metric

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X] {m : MeasurableSpace X} (μ : Measure X)
  [IsOpenPosMeasure μ]

/--
theorem `measure_eball_pos` / 定理 `measure_eball_pos`

English:
theorem measure_eball_pos
  given: (x : X) {r : Real>=0∞} (hr : r != 0)
  statement: 0 < μ (eball x r)
  proof: isOpen_eball.measure_pos μ ⟨x, mem_eball_self hr.bot_lt⟩

中文:
定理 measure_eball_pos
  条件: (x : X) {r : 实数>=0∞} (hr : r != 0)
  结论: 0 < μ (eball x r)
  证明: isOpen_eball.measure_pos μ ⟨x, mem_eball_self hr.bot_lt⟩

Depends on / 依赖: bot_lt, hr.bot_lt, isOpen_eball, isOpen_eball.measure_pos, measure_pos, mem_eball_self
-/
theorem measure_eball_pos (x : X) {r : Real>=0∞} (hr : r != 0) : 0 < μ (eball x r) :=
  isOpen_eball.measure_pos μ ⟨x, mem_eball_self hr.bot_lt⟩

/--
theorem `measure_closedEBall_pos` / 定理 `measure_closedEBall_pos`

English:
theorem measure_closedEBall_pos
  given: (x : X) {r : Real>=0∞} (hr : r != 0)
  statement: 0 < μ (closedEBall x r)
  proof: (measure_eball_pos μ x hr).trans_le (measure_mono eball_subset_closedEBall)

中文:
定理 measure_closedEBall_pos
  条件: (x : X) {r : 实数>=0∞} (hr : r != 0)
  结论: 0 < μ (closedEBall x r)
  证明: (measure_eball_pos μ x hr).trans_le (measure_mono eball_subset_closedEBall)

Depends on / 依赖: eball_subset_closedEBall, measure_eball_pos, measure_mono, trans_le
-/
theorem measure_closedEBall_pos (x : X) {r : Real>=0∞} (hr : r != 0) : 0 < μ (closedEBall x r) :=
  (measure_eball_pos μ x hr).trans_le (measure_mono eball_subset_closedEBall)

end Metric

@[deprecated (since := "2026-01-24")]
alias EMetric.measure_ball_pos := Metric.measure_eball_pos

@[deprecated (since := "2026-01-24")]
alias EMetric.measure_closedBall_pos := Metric.measure_closedEBall_pos

section MeasureZero
/-! ## Meagre sets and measure zero
In general, neither of meagre and measure zero implies the other.
- The set of Liouville numbers is a Lebesgue measure zero subset of ℝ, but is not meagre.
  (In fact, its complement is meagre. See `Real.disjoint_residual_ae`.)

- The complement of the set of Liouville numbers in $[0,1]$ is meagre and has measure 1.
  For another counterexample, for all $α ∈ (0,1)$, there is a generalised Cantor set $C ⊆ [0,1]$
  of measure `α`. Cantor sets are nowhere dense (hence meagre). Taking a countable union of
  fat Cantor sets whose measure approaches 1 even yields a meagre set of measure 1.

However, with respect to a measure which is positive on non-empty open sets, *closed* measure
zero sets are nowhere dense and σ-compact measure zero sets in a Hausdorff space are meagre.
-/

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {s : Set X}
  {μ : Measure X} [IsOpenPosMeasure μ]

/--
lemma `IsNowhereDense.of_isClosed_null` / 引理 `IsNowhereDense.of_isClosed_null`

English:
lemma IsNowhereDense.of_isClosed_null
  given: (h₁s : IsClosed s) (h₂s : μ s = 0)
  proof: h₁s.isNowhereDense_iff.mpr (interior_eq_empty_of_null h₂s)

中文:
引理 IsNowhereDense.of_isClosed_null
  条件: (h₁s : 是闭集 s) (h₂s : μ s = 0)
  证明: h₁s.isNowhereDense_iff.mpr (interior_eq_empty_of_null h₂s)

Depends on / 依赖: interior_eq_empty_of_null, isNowhereDense_iff, s.isNowhereDense_iff.mpr
-/
lemma IsNowhereDense.of_isClosed_null (h₁s : IsClosed s) (h₂s : μ s = 0) :
    IsNowhereDense s := h₁s.isNowhereDense_iff.mpr (interior_eq_empty_of_null h₂s)

/--
lemma `IsMeagre.of_isSigmaCompact_null` / 引理 `IsMeagre.of_isSigmaCompact_null`

English:
lemma IsMeagre.of_isSigmaCompact_null
  given: [T2Space X] (h₁s : IsSigmaCompact s) (h₂s : μ s = 0)
  proof: by
  rcases h₁s with ⟨K, hcompact, hcover⟩
  have h (n : Nat) : IsNowhereDense (K n) := by
    have : μ (K n) = 0 := measure_mono_null (hcover ▸ subset_iUnion K n) h₂s
    exact .of_isClosed_null (hcompact n).isClosed this
  rw [isMeagre_iff_countable_union_isNowhereDense]
  exact ⟨range K, fun t ⟨n

中文:
引理 IsMeagre.of_isSigmaCompact_null
  条件: [T2空间 X] (h₁s : IsSigmaCompact s) (h₂s : μ s = 0)
  证明: by
  rcases h₁s with ⟨K, hcompact, hcover⟩
  have h (n : Nat) : IsNowhereDense (K n) := by
    have : μ (K n) = 0 := measure_mono_null (hcover ▸ subset_iUnion K n) h₂s
    exact .of_isClosed_null (hcompact n).isClosed this
  rw [isMeagre_iff_countable_union_isNowhereDense]
  exact ⟨range K, fun t ⟨n

Depends on / 依赖: IsNowhereDense, countable_range, hcompact, hcover, hcover.symm.subset, isClosed, isMeagre_iff_countable_union_isNowhereDense, measure_mono_null, of_isClosed_null, subset, subset_iUnion
-/
lemma IsMeagre.of_isSigmaCompact_null [T2Space X] (h₁s : IsSigmaCompact s) (h₂s : μ s = 0) :
    IsMeagre s := by
  rcases h₁s with ⟨K, hcompact, hcover⟩
  have h (n : Nat) : IsNowhereDense (K n) := by
    have : μ (K n) = 0 := measure_mono_null (hcover ▸ subset_iUnion K n) h₂s
    exact .of_isClosed_null (hcompact n).isClosed this
  rw [isMeagre_iff_countable_union_isNowhereDense]
  exact ⟨range K, fun t ⟨n, hn⟩ => hn ▸ h n, countable_range K, hcover.symm.subset⟩

end MeasureZero
