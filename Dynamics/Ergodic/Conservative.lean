/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Combinatorics.Pigeonhole

/-!
# Conservative systems

In this file we define `f : α → α` to be a *conservative* system w.r.t. a measure `μ` if `f` is
non-singular (`MeasureTheory.QuasiMeasurePreserving`) and for every measurable set `s` of
positive measure at least one point `x ∈ s` returns back to `s` after some number of iterations of
`f`. There are several properties that look like they are stronger than this one but actually follow
from it:

* `MeasureTheory.Conservative.frequently_measure_inter_ne_zero`,
  `MeasureTheory.Conservative.exists_gt_measure_inter_ne_zero`: if `μ s ≠ 0`, then for infinitely
  many `n`, the measure of `s ∩ f^[n] ⁻¹' s` is positive.

* `MeasureTheory.Conservative.measure_mem_forall_ge_image_notMem_eq_zero`,
  `MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`: a.e. every point of `s` visits `s`
  infinitely many times (Poincaré recurrence theorem).

We also prove the topological Poincaré recurrence theorem
`MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds`. Let `f : α → α` be a conservative
dynamical system on a topological space with second countable topology and measurable open
sets. Then almost every point `x : α` is recurrent: it visits every neighborhood `s ∈ 𝓝 x`
infinitely many times.

## Tags

conservative dynamical system, Poincare recurrence theorem
-/

public section


noncomputable section

namespace MeasureTheory

open Set Filter Finset Function TopologicalSpace Topology

variable {α : Type*} [MeasurableSpace α] {f : α -> α} {s : Set α} {μ : Measure α}

open Measure

/--
Definition of `Conservative` / `Conservative` 的定义

English:
structure Conservative
  parameters: (f : α -> α) (μ : Measure α)
  extends: QuasiMeasurePreserving f μ μ
  axioms and operations (1):
    - exists_mem_iterate_mem' : forall ⦃s⦄, MeasurableSet s -> μ s != 0 -> exists x in s, exists m != 0, f^[m] x in s

中文:
结构 余nservative
  参数: (f : α -> α) (μ : 测度 α)
  继承: 拟保测 f μ μ
  公理与运算 (1 个):
    - exists_mem_iterate_mem' : 对任意 ⦃s⦄, 可测集 s -> μ s != 0 -> 存在 x in s, 存在 m != 0, f^[m] x in s

Depends on / 依赖: exists_mem_iterate_mem, h.exists_mem_iterate_mem, h.quasiMeasurePreserving, hsm.nullMeasurableSet, nullMeasurableSet, quasiMeasurePreserving
-/
structure Conservative (f : α -> α) (μ : Measure α) : Prop extends QuasiMeasurePreserving f μ μ where
  /-- If `f` is a conservative self-map and `s` is a measurable set of nonzero measure,
  then there exists a point `x ∈ s` that returns to `s` under a non-zero iteration of `f`. -/
  exists_mem_iterate_mem' : forall ⦃s⦄, MeasurableSet s -> μ s != 0 -> exists x in s, exists m != 0, f^[m] x in s

/--
theorem `MeasurePreserving.conservative` / 定理 `MeasurePreserving.conservative`

English:
theorem MeasurePreserving.conservative
  given: [IsFiniteMeasure μ] (h : MeasurePreserving f μ μ)
  proof: ⟨h.quasiMeasurePreserving, fun _ hsm h0 => h.exists_mem_iterate_mem hsm.nullMeasurableSet h0⟩

中文:
定理 保测.conservative
  条件: [是有限测度 μ] (h : 保测 f μ μ)
  证明: ⟨h.quasiMeasurePreserving, fun _ hsm h0 => h.exists_mem_iterate_mem hsm.nullMeasurableSet h0⟩
-/
protected theorem MeasurePreserving.conservative [IsFiniteMeasure μ] (h : MeasurePreserving f μ μ) :
    Conservative f μ :=
  ⟨h.quasiMeasurePreserving, fun _ hsm h0 => h.exists_mem_iterate_mem hsm.nullMeasurableSet h0⟩

namespace Conservative

/--
theorem `id` / 定理 `id`

English:
theorem id
  given: (μ : Measure α)
  statement: Conservative id μ
  proof: { toQuasiMeasurePreserving := QuasiMeasurePreserving.id μ
    exists_mem_iterate_mem' := fun _ _ h0 => by
      simpa [exists_ne] using! nonempty_of_measure_ne_zero h0 }

中文:
定理 id
  条件: (μ : 测度 α)
  结论: 余nservative id μ
  证明: { toQuasiMeasurePreserving := QuasiMeasurePreserving.id μ
    exists_mem_iterate_mem' := fun _ _ h0 => by
      simpa [exists_ne] using! nonempty_of_measure_ne_zero h0 }
-/
protected theorem id (μ : Measure α) : Conservative id μ :=
  { toQuasiMeasurePreserving := QuasiMeasurePreserving.id μ
    exists_mem_iterate_mem' := fun _ _ h0 => by
      simpa [exists_ne] using! nonempty_of_measure_ne_zero h0 }

/--
theorem `of_absolutelyContinuous` / 定理 `of_absolutelyContinuous`

English:
theorem of_absolutelyContinuous
  statement: {ν : Measure α} (h : Conservative f μ) (hν : ν ≪ μ)
  proof: ⟨h', fun _ hsm h0 => h.exists_mem_iterate_mem' hsm (mt (@hν _) h0)⟩

中文:
定理 of_absolutelyContinuous
  结论: {ν : 测度 α} (h : 余nservative f μ) (hν : ν ≪ μ)
  证明: ⟨h', fun _ hsm h0 => h.exists_mem_iterate_mem' hsm (mt (@hν _) h0)⟩

Depends on / 依赖: exists_mem_iterate_mem, h.exists_mem_iterate_mem
-/
theorem of_absolutelyContinuous {ν : Measure α} (h : Conservative f μ) (hν : ν ≪ μ)
    (h' : QuasiMeasurePreserving f ν ν) : Conservative f ν :=
  ⟨h', fun _ hsm h0 => h.exists_mem_iterate_mem' hsm (mt (@hν _) h0)⟩

/--
theorem `measureRestrict` / 定理 `measureRestrict`

English:
theorem measureRestrict
  given: (h : Conservative f μ) (hs : MapsTo f s s)
  proof: .of_absolutelyContinuous h (absolutelyContinuous_of_le restrict_le_self)
    h.toQuasiMeasurePreserving.restrict hs

中文:
定理 measureRestrict
  条件: (h : 余nservative f μ) (hs : 映射到 f s s)
  证明: .of_absolutelyContinuous h (absolutelyContinuous_of_le restrict_le_self)
    h.toQuasiMeasurePreserving.restrict hs

Depends on / 依赖: absolutelyContinuous_of_le, h.toQuasiMeasurePreserving.restrict, of_absolutelyContinuous, restrict, restrict_le_self, toQuasiMeasurePreserving
-/
theorem measureRestrict (h : Conservative f μ) (hs : MapsTo f s s) :
    Conservative f (μ.restrict s) :=
.of_absolutelyContinuous h (absolutelyContinuous_of_le restrict_le_self)
    h.toQuasiMeasurePreserving.restrict hs

/--
theorem `congr_ae` / 定理 `congr_ae`

English:
theorem congr_ae
  given: {ν : Measure α} (hf : Conservative f μ) (h : ae μ = ae ν)
  proof: .of_absolutelyContinuous hf h.ge.absolutelyContinuous_of_ae
    hf.toQuasiMeasurePreserving.mono h.ge.absolutelyContinuous_of_ae h.le.absolutelyContinuous_of_ae

中文:
定理 congr_ae
  条件: {ν : 测度 α} (hf : 余nservative f μ) (h : ae μ = ae ν)
  证明: .of_absolutelyContinuous hf h.ge.absolutelyContinuous_of_ae
    hf.toQuasiMeasurePreserving.mono h.ge.absolutelyContinuous_of_ae h.le.absolutelyContinuous_of_ae

Depends on / 依赖: absolutelyContinuous_of_ae, h.ge.absolutelyContinuous_of_ae, h.le.absolutelyContinuous_of_ae, hf.toQuasiMeasurePreserving.mono, of_absolutelyContinuous, toQuasiMeasurePreserving
-/
theorem congr_ae {ν : Measure α} (hf : Conservative f μ) (h : ae μ = ae ν) :
    Conservative f ν :=
.of_absolutelyContinuous hf h.ge.absolutelyContinuous_of_ae
    hf.toQuasiMeasurePreserving.mono h.ge.absolutelyContinuous_of_ae h.le.absolutelyContinuous_of_ae

/--
theorem `_root_.MeasureTheory.conservative_congr` / 定理 `_root_.MeasureTheory.conservative_congr`

English:
theorem _root_.MeasureTheory.conservative_congr
  given: {ν : Measure α} (h : ae μ = ae ν)
  proof: ⟨(congr_ae · h), (congr_ae · h.symm)⟩

中文:
定理 _root_.测度论.conservative_congr
  条件: {ν : 测度 α} (h : ae μ = ae ν)
  证明: ⟨(congr_ae · h), (congr_ae · h.symm)⟩

Depends on / 依赖: congr_ae, h.symm
-/
theorem _root_.MeasureTheory.conservative_congr {ν : Measure α} (h : ae μ = ae ν) :
    Conservative f μ ↔ Conservative f ν :=
  ⟨(congr_ae · h), (congr_ae · h.symm)⟩

/--
theorem `exists_mem_iterate_mem` / 定理 `exists_mem_iterate_mem`

English:
theorem exists_mem_iterate_mem
  statement: (hf : Conservative f μ)
  proof: by
  rcases hsm.exists_measurable_subset_ae_eq with ⟨t, hsub, htm, hts⟩
  rcases hf.exists_mem_iterate_mem' htm (by rwa [measure_congr hts]) with ⟨x, hxt, m, hm₀, hmt⟩
  exact ⟨x, hsub hxt, m, hm₀, hsub hmt⟩

中文:
定理 存在_mem_iterate_mem
  结论: (hf : 余nservative f μ)
  证明: by
  rcases hsm.exists_measurable_subset_ae_eq with ⟨t, hsub, htm, hts⟩
  rcases hf.exists_mem_iterate_mem' htm (by rwa [measure_congr hts]) with ⟨x, hxt, m, hm₀, hmt⟩
  exact ⟨x, hsub hxt, m, hm₀, hsub hmt⟩

Depends on / 依赖: exists_measurable_subset_ae_eq, exists_mem_iterate_mem, hf.exists_mem_iterate_mem, hsm.exists_measurable_subset_ae_eq, measure_congr
-/
theorem exists_mem_iterate_mem (hf : Conservative f μ)
    (hsm : NullMeasurableSet s μ) (hs₀ : μ s != 0) :
    exists x in s, exists m != 0, f^[m] x in s := by
  rcases hsm.exists_measurable_subset_ae_eq with ⟨t, hsub, htm, hts⟩
  rcases hf.exists_mem_iterate_mem' htm (by rwa [measure_congr hts]) with ⟨x, hxt, m, hm₀, hmt⟩
  exact ⟨x, hsub hxt, m, hm₀, hsub hmt⟩

/--
theorem `frequently_measure_inter_ne_zero` / 定理 `frequently_measure_inter_ne_zero`

English:
theorem frequently_measure_inter_ne_zero
  statement: (hf : Conservative f μ) (hs : NullMeasurableSet s μ)
  proof: by
  set t : Nat -> Set α := fun n => s inter f^[n] ⁻¹' s
  -- Assume that `μ (t n) ≠ 0`, where `t n = s ∩ f^[n] ⁻¹' s`, only for finitely many `n`.
  by_contra H
  -- Let `N` be the maximal `n` such that `μ (t n) ≠ 0`.
  obtain ⟨N, hN, hmax⟩ : exists N, μ (t N) != 0 ∧ forall n > N, μ (t n) = 0 := by
    rw [Nat.frequently_atTop_iff_infinite]; rw [not_infinite] at H
    convert! exists_max_image _ (·) H ⟨0, by simpa⟩ using 4
    rw [gt_iff_lt]; rw [← not_le]; rw [not_imp_comm]; rw [mem_ofPred]
  have htm {n : Nat} : NullMeasurableSet (t n) μ :=
hs.inter hs.preimage hf.toQuasiMeasurePreserving.iterate n
  -- Then all `t n`, `n > N`, are null sets, hence `T = t N \ ⋃ n > N, t n` has positive measure.
  set T := t N \ ⋃ n > N, t n with hT
  have hμT : μ T != 0 := by
    rwa [hT, measure_sdiff_null]
    exact (measure_biUnion_null_iff {n | N < n}.to_countable).2 hmax
have hTm : NullMeasurableSet T μ := htm.diff .biUnion {n | N < n}.to_countable fun _ _ => htm
  -- Take `x ∈ T` and `m ≠ 0` such that `f^[m] x ∈ T`.
  rcases hf.exists_mem_iterate_mem hTm hμT with ⟨x, hxt, m, hm₀, hmt⟩
  -- Then `N + m > N`, `x ∈ s`, and `f^[N + m] x = f^[N] (f^[m] x) ∈ s`.
  -- This contradicts `x ∈ T ⊆ (⋃ n > N, t n)ᶜ`.
refine hxt.2 mem_iUnion₂.2 ⟨N + m, ?_, hxt.1.1, ?_⟩
  · simpa [pos_iff_ne_zero]
  · simpa only [iterate_add] using! hmt.1.2

中文:
定理 frequently_measure_inter_ne_zero
  结论: (hf : 余nservative f μ) (hs : NullMeasurableSet s μ)
  证明: by
  set t : Nat -> Set α := fun n => s inter f^[n] ⁻¹' s
  -- Assume that `μ (t n) ≠ 0`, where `t n = s ∩ f^[n] ⁻¹' s`, only for finitely many `n`.
  by_contra H
  -- Let `N` be the maximal `n` such that `μ (t n) ≠ 0`.
  obtain ⟨N, hN, hmax⟩ : exists N, μ (t N) != 0 ∧ forall n > N, μ (t n) = 0 := by
    rw [Nat.frequently_atTop_iff_infinite]; rw [not_infinite] at H
    convert! exists_max_image _ (·) H ⟨0, by simpa⟩ using 4
    rw [gt_iff_lt]; rw [← not_le]; rw [not_imp_comm]; rw [mem_ofPred]
  have htm {n : Nat} : NullMeasurableSet (t n) μ :=
hs.inter hs.preimage hf.toQuasiMeasurePreserving.iterate n
  -- Then all `t n`, `n > N`, are null sets, hence `T = t N \ ⋃ n > N, t n` has positive measure.
  set T := t N \ ⋃ n > N, t n with hT
  have hμT : μ T != 0 := by
    rwa [hT, measure_sdiff_null]
    exact (measure_biUnion_null_iff {n | N < n}.to_countable).2 hmax
have hTm : NullMeasurableSet T μ := htm.diff .biUnion {n | N < n}.to_countable fun _ _ => htm
  -- Take `x ∈ T` and `m ≠ 0` such that `f^[m] x ∈ T`.
  rcases hf.exists_mem_iterate_mem hTm hμT with ⟨x, hxt, m, hm₀, hmt⟩
  -- Then `N + m > N`, `x ∈ s`, and `f^[N + m] x = f^[N] (f^[m] x) ∈ s`.
  -- This contradicts `x ∈ T ⊆ (⋃ n > N, t n)ᶜ`.
refine hxt.2 mem_iUnion₂.2 ⟨N + m, ?_, hxt.1.1, ?_⟩
  · simpa [pos_iff_ne_zero]
  · simpa only [iterate_add] using! hmt.1.2
-/
theorem frequently_measure_inter_ne_zero (hf : Conservative f μ) (hs : NullMeasurableSet s μ)
    (h0 : μ s != 0) : existsᶠ m in atTop, μ (s inter f^[m] ⁻¹' s) != 0 := by
  set t : Nat -> Set α := fun n => s inter f^[n] ⁻¹' s
  -- Assume that `μ (t n) ≠ 0`, where `t n = s ∩ f^[n] ⁻¹' s`, only for finitely many `n`.
  by_contra H
  -- Let `N` be the maximal `n` such that `μ (t n) ≠ 0`.
  obtain ⟨N, hN, hmax⟩ : exists N, μ (t N) != 0 ∧ forall n > N, μ (t n) = 0 := by
    rw [Nat.frequently_atTop_iff_infinite]; rw [not_infinite] at H
    convert! exists_max_image _ (·) H ⟨0, by simpa⟩ using 4
    rw [gt_iff_lt]; rw [← not_le]; rw [not_imp_comm]; rw [mem_ofPred]
  have htm {n : Nat} : NullMeasurableSet (t n) μ :=
hs.inter hs.preimage hf.toQuasiMeasurePreserving.iterate n
  -- Then all `t n`, `n > N`, are null sets, hence `T = t N \ ⋃ n > N, t n` has positive measure.
  set T := t N \ ⋃ n > N, t n with hT
  have hμT : μ T != 0 := by
    rwa [hT, measure_sdiff_null]
    exact (measure_biUnion_null_iff {n | N < n}.to_countable).2 hmax
have hTm : NullMeasurableSet T μ := htm.diff .biUnion {n | N < n}.to_countable fun _ _ => htm
  -- Take `x ∈ T` and `m ≠ 0` such that `f^[m] x ∈ T`.
  rcases hf.exists_mem_iterate_mem hTm hμT with ⟨x, hxt, m, hm₀, hmt⟩
  -- Then `N + m > N`, `x ∈ s`, and `f^[N + m] x = f^[N] (f^[m] x) ∈ s`.
  -- This contradicts `x ∈ T ⊆ (⋃ n > N, t n)ᶜ`.
refine hxt.2 mem_iUnion₂.2 ⟨N + m, ?_, hxt.1.1, ?_⟩
  · simpa [pos_iff_ne_zero]
  · simpa only [iterate_add] using! hmt.1.2

/--
theorem `exists_gt_measure_inter_ne_zero` / 定理 `exists_gt_measure_inter_ne_zero`

English:
theorem exists_gt_measure_inter_ne_zero
  statement: (hf : Conservative f μ) (hs : NullMeasurableSet s μ)
  proof: let ⟨m, hm, hmN⟩ :=
    ((hf.frequently_measure_inter_ne_zero hs h0).and_eventually (eventually_gt_atTop N)).exists
  ⟨m, hmN, hm⟩

中文:
定理 存在_gt_measure_inter_ne_zero
  结论: (hf : 余nservative f μ) (hs : NullMeasurableSet s μ)
  证明: let ⟨m, hm, hmN⟩ :=
    ((hf.frequently_measure_inter_ne_zero hs h0).and_eventually (eventually_gt_atTop N)).exists
  ⟨m, hmN, hm⟩

Depends on / 依赖: and_eventually, eventually_gt_atTop, frequently_measure_inter_ne_zero, hf.frequently_measure_inter_ne_zero
-/
theorem exists_gt_measure_inter_ne_zero (hf : Conservative f μ) (hs : NullMeasurableSet s μ)
    (h0 : μ s != 0) (N : Nat) : exists m > N, μ (s inter f^[m] ⁻¹' s) != 0 :=
  let ⟨m, hm, hmN⟩ :=
    ((hf.frequently_measure_inter_ne_zero hs h0).and_eventually (eventually_gt_atTop N)).exists
  ⟨m, hmN, hm⟩

/--
theorem `measure_mem_forall_ge_image_notMem_eq_zero` / 定理 `measure_mem_forall_ge_image_notMem_eq_zero`

English:
theorem measure_mem_forall_ge_image_notMem_eq_zero
  statement: (hf : Conservative f μ)
  proof: by
  by_contra H
  have : NullMeasurableSet (s inter { x | forall m >= n, f^[m] x ∉ s }) μ := by
    simp only [ofPred_forall, ← compl_ofPred]
exact hs.inter .biInter (to_countable _) fun m _ =>
      (hs.preimage <| hf.toQuasiMeasurePreserving.iterate m).compl
  rcases (hf.exists_gt_measure_inter_ne_zero this H) n with ⟨m, hmn, hm⟩
  rcases nonempty_of_measure_ne_zero hm with ⟨x, ⟨_, hxn⟩, hxm, -⟩
  exact hxn m hmn.lt.le hxm

中文:
定理 measure_mem_对任意_ge_image_notMem_eq_zero
  结论: (hf : 余nservative f μ)
  证明: by
  by_contra H
  have : NullMeasurableSet (s inter { x | forall m >= n, f^[m] x ∉ s }) μ := by
    simp only [ofPred_forall, ← compl_ofPred]
exact hs.inter .biInter (to_countable _) fun m _ =>
      (hs.preimage <| hf.toQuasiMeasurePreserving.iterate m).compl
  rcases (hf.exists_gt_measure_inter_ne_zero this H) n with ⟨m, hmn, hm⟩
  rcases nonempty_of_measure_ne_zero hm with ⟨x, ⟨_, hxn⟩, hxm, -⟩
  exact hxn m hmn.lt.le hxm

Depends on / 依赖: IsPreprimitive, IsPreprimitive.isQuasiPreprimitive, NullMeasurableSet, biInter, compl_ofPred, exists_gt_measure_inter_ne_zero, hf.exists_gt_measure_inter_ne_zero, hf.toQuasiMeasurePreserving.iterate, hmn.lt.le, hs.inter, hs.preimage, isQuasiPreprimitive, iterate, nonempty_of_measure_ne_zero, ofPred_forall, preimage, toQuasiMeasurePreserving, to_countable
-/
theorem measure_mem_forall_ge_image_notMem_eq_zero (hf : Conservative f μ)
    (hs : NullMeasurableSet s μ) (n : Nat) :
    μ ({ x in s | forall m >= n, f^[m] x ∉ s }) = 0 := by
  by_contra H
  have : NullMeasurableSet (s inter { x | forall m >= n, f^[m] x ∉ s }) μ := by
    simp only [ofPred_forall, ← compl_ofPred]
exact hs.inter .biInter (to_countable _) fun m _ =>
      (hs.preimage <| hf.toQuasiMeasurePreserving.iterate m).compl
  rcases (hf.exists_gt_measure_inter_ne_zero this H) n with ⟨m, hmn, hm⟩
  rcases nonempty_of_measure_ne_zero hm with ⟨x, ⟨_, hxn⟩, hxm, -⟩
  exact hxn m hmn.lt.le hxm

/--
theorem `ae_mem_imp_frequently_image_mem` / 定理 `ae_mem_imp_frequently_image_mem`

English:
theorem ae_mem_imp_frequently_image_mem
  given: (hf : Conservative f μ) (hs : NullMeasurableSet s μ)
  proof: by
  simp only [frequently_atTop, @forall_comm (_ in s), ae_all_iff]
  intro n
  filter_upwards
    [measure_eq_zero_iff_ae_notMem.1 (hf.measure_mem_forall_ge_image_notMem_eq_zero hs n)]
  simp

中文:
定理 ae_mem_imp_frequently_image_mem
  条件: (hf : 余nservative f μ) (hs : NullMeasurableSet s μ)
  证明: by
  simp only [frequently_atTop, @forall_comm (_ in s), ae_all_iff]
  intro n
  filter_upwards
    [measure_eq_zero_iff_ae_notMem.1 (hf.measure_mem_forall_ge_image_notMem_eq_zero hs n)]
  simp

Depends on / 依赖: ae_all_iff, filter_upwards, forall_comm, frequently_atTop, hf.measure_mem_forall_ge_image_notMem_eq_zero, measure_eq_zero_iff_ae_notMem, measure_mem_forall_ge_image_notMem_eq_zero
-/
theorem ae_mem_imp_frequently_image_mem (hf : Conservative f μ) (hs : NullMeasurableSet s μ) :
    forallᵐ x ∂μ, x in s -> existsᶠ n in atTop, f^[n] x in s := by
  simp only [frequently_atTop, @forall_comm (_ in s), ae_all_iff]
  intro n
  filter_upwards
    [measure_eq_zero_iff_ae_notMem.1 (hf.measure_mem_forall_ge_image_notMem_eq_zero hs n)]
  simp

/--
theorem `inter_frequently_image_mem_ae_eq` / 定理 `inter_frequently_image_mem_ae_eq`

English:
theorem inter_frequently_image_mem_ae_eq
  given: (hf : Conservative f μ) (hs : NullMeasurableSet s μ)
  proof: inter_eventuallyEq_left.2 hf.ae_mem_imp_frequently_image_mem hs

中文:
定理 inter_frequently_image_mem_ae_eq
  条件: (hf : 余nservative f μ) (hs : NullMeasurableSet s μ)
  证明: inter_eventuallyEq_left.2 hf.ae_mem_imp_frequently_image_mem hs

Depends on / 依赖: ae_mem_imp_frequently_image_mem, hf.ae_mem_imp_frequently_image_mem, inter_eventuallyEq_left
-/
theorem inter_frequently_image_mem_ae_eq (hf : Conservative f μ) (hs : NullMeasurableSet s μ) :
    (s inter { x | existsᶠ n in atTop, f^[n] x in s } : Set α) =ᵐ[μ] s :=
inter_eventuallyEq_left.2 hf.ae_mem_imp_frequently_image_mem hs

/--
theorem `measure_inter_frequently_image_mem_eq` / 定理 `measure_inter_frequently_image_mem_eq`

English:
theorem measure_inter_frequently_image_mem_eq
  given: (hf : Conservative f μ) (hs : NullMeasurableSet s μ)
  proof: measure_congr (hf.inter_frequently_image_mem_ae_eq hs)

中文:
定理 measure_inter_frequently_image_mem_eq
  条件: (hf : 余nservative f μ) (hs : NullMeasurableSet s μ)
  证明: measure_congr (hf.inter_frequently_image_mem_ae_eq hs)

Depends on / 依赖: hf.inter_frequently_image_mem_ae_eq, inter_frequently_image_mem_ae_eq, measure_congr
-/
theorem measure_inter_frequently_image_mem_eq (hf : Conservative f μ) (hs : NullMeasurableSet s μ) :
    μ (s inter { x | existsᶠ n in atTop, f^[n] x in s }) = μ s :=
  measure_congr (hf.inter_frequently_image_mem_ae_eq hs)

/--
theorem `ae_forall_image_mem_imp_frequently_image_mem` / 定理 `ae_forall_image_mem_imp_frequently_image_mem`

English:
theorem ae_forall_image_mem_imp_frequently_image_mem
  statement: (hf : Conservative f μ)
  proof: by
  refine ae_all_iff.2 fun k => ?_
  refine (hf.ae_mem_imp_frequently_image_mem
    (hs.preimage <| hf.toQuasiMeasurePreserving.iterate k)).mono fun x hx hk => ?_
  rw [← map_add_atTop_eq_nat k]; rw [frequently_map]
  refine (hx hk).mono fun n hn => ?_
  rwa [add_comm, iterate_add_apply]

中文:
定理 ae_对任意_image_mem_imp_frequently_image_mem
  结论: (hf : 余nservative f μ)
  证明: by
  refine ae_all_iff.2 fun k => ?_
  refine (hf.ae_mem_imp_frequently_image_mem
    (hs.preimage <| hf.toQuasiMeasurePreserving.iterate k)).mono fun x hx hk => ?_
  rw [← map_add_atTop_eq_nat k]; rw [frequently_map]
  refine (hx hk).mono fun n hn => ?_
  rwa [add_comm, iterate_add_apply]

Depends on / 依赖: add_comm, ae_all_iff, ae_mem_imp_frequently_image_mem, frequently_map, hf.ae_mem_imp_frequently_image_mem, hf.toQuasiMeasurePreserving.iterate, hs.preimage, iterate, iterate_add_apply, map_add_atTop_eq_nat, preimage, toQuasiMeasurePreserving
-/
theorem ae_forall_image_mem_imp_frequently_image_mem (hf : Conservative f μ)
    (hs : NullMeasurableSet s μ) : forallᵐ x ∂μ, forall k, f^[k] x in s -> existsᶠ n in atTop, f^[n] x in s := by
  refine ae_all_iff.2 fun k => ?_
  refine (hf.ae_mem_imp_frequently_image_mem
    (hs.preimage <| hf.toQuasiMeasurePreserving.iterate k)).mono fun x hx hk => ?_
  rw [← map_add_atTop_eq_nat k]; rw [frequently_map]
  refine (hx hk).mono fun n hn => ?_
  rwa [add_comm, iterate_add_apply]

/--
theorem `frequently_ae_mem_and_frequently_image_mem` / 定理 `frequently_ae_mem_and_frequently_image_mem`

English:
theorem frequently_ae_mem_and_frequently_image_mem
  statement: (hf : Conservative f μ)
  proof: ((frequently_ae_mem_iff.2 h0).and_eventually (hf.ae_mem_imp_frequently_image_mem hs)).mono
    fun _ hx => ⟨hx.1, hx.2 hx.1⟩

中文:
定理 frequently_ae_mem_and_frequently_image_mem
  结论: (hf : 余nservative f μ)
  证明: ((frequently_ae_mem_iff.2 h0).and_eventually (hf.ae_mem_imp_frequently_image_mem hs)).mono
    fun _ hx => ⟨hx.1, hx.2 hx.1⟩

Depends on / 依赖: ae_mem_imp_frequently_image_mem, and_eventually, frequently_ae_mem_iff, hf.ae_mem_imp_frequently_image_mem
-/
theorem frequently_ae_mem_and_frequently_image_mem (hf : Conservative f μ)
    (hs : NullMeasurableSet s μ) (h0 : μ s != 0) : existsᵐ x ∂μ, x in s ∧ existsᶠ n in atTop, f^[n] x in s :=
  ((frequently_ae_mem_iff.2 h0).and_eventually (hf.ae_mem_imp_frequently_image_mem hs)).mono
    fun _ hx => ⟨hx.1, hx.2 hx.1⟩

/--
theorem `ae_frequently_mem_of_mem_nhds` / 定理 `ae_frequently_mem_of_mem_nhds`

English:
theorem ae_frequently_mem_of_mem_nhds
  statement: [TopologicalSpace α] [SecondCountableTopology α]
  proof: by
  have : forall s in countableBasis α, forallᵐ x ∂μ, x in s -> existsᶠ n in atTop, f^[n] x in s := fun s hs =>
    h.ae_mem_imp_frequently_image_mem (isOpen_of_mem_countableBasis hs).nullMeasurableSet
  refine ((ae_ball_iff <| countable_countableBasis α).2 this).mono fun x hx s hs => ?_
  rcases (isBasis_countableBasis α).mem_nhds_iff.1 hs with ⟨o, hoS, hxo, hos⟩
  exact (hx o hoS hxo).mono fun n hn => hos hn

中文:
定理 ae_frequently_mem_of_mem_nhds
  结论: [拓扑空间 α] [第二可数拓扑 α]
  证明: by
  have : forall s in countableBasis α, forallᵐ x ∂μ, x in s -> existsᶠ n in atTop, f^[n] x in s := fun s hs =>
    h.ae_mem_imp_frequently_image_mem (isOpen_of_mem_countableBasis hs).nullMeasurableSet
  refine ((ae_ball_iff <| countable_countableBasis α).2 this).mono fun x hx s hs => ?_
  rcases (isBasis_countableBasis α).mem_nhds_iff.1 hs with ⟨o, hoS, hxo, hos⟩
  exact (hx o hoS hxo).mono fun n hn => hos hn

Depends on / 依赖: ae_ball_iff, ae_mem_imp_frequently_image_mem, countableBasis, countable_countableBasis, h.ae_mem_imp_frequently_image_mem, isBasis_countableBasis, isOpen_of_mem_countableBasis, mem_nhds_iff, nullMeasurableSet
-/
theorem ae_frequently_mem_of_mem_nhds [TopologicalSpace α] [SecondCountableTopology α]
    [OpensMeasurableSpace α] {f : α -> α} {μ : Measure α} (h : Conservative f μ) :
    forallᵐ x ∂μ, forall s in 𝓝 x, existsᶠ n in atTop, f^[n] x in s := by
  have : forall s in countableBasis α, forallᵐ x ∂μ, x in s -> existsᶠ n in atTop, f^[n] x in s := fun s hs =>
    h.ae_mem_imp_frequently_image_mem (isOpen_of_mem_countableBasis hs).nullMeasurableSet
  refine ((ae_ball_iff <| countable_countableBasis α).2 this).mono fun x hx s hs => ?_
  rcases (isBasis_countableBasis α).mem_nhds_iff.1 hs with ⟨o, hoS, hxo, hos⟩
  exact (hx o hoS hxo).mono fun n hn => hos hn

/--
theorem `iterate` / 定理 `iterate`

English:
theorem iterate
  given: (hf : Conservative f μ) (n : Nat)
  statement: Conservative f^[n] μ
  proof: by
  -- Discharge the trivial case `n = 0`
  rcases n with - | n
  · exact Conservative.id μ
  refine ⟨hf.1.iterate _, fun s hs hs0 => ?_⟩
  rcases (hf.frequently_ae_mem_and_frequently_image_mem hs.nullMeasurableSet hs0).exists
    with ⟨x, _, hx⟩
  /- We take a point `x ∈ s` such that `f^[k] x ∈ s` for infinitely many values of `k`,
    then we choose two of these values `k < l` such that `k ≡ l [MOD (n + 1)]`.
    Then `f^[k] x ∈ s` and `f^[n + 1]^[(l - k) / (n + 1)] (f^[k] x) = f^[l] x ∈ s`. -/
  rw [Nat.frequently_atTop_iff_infinite] at hx
  rcases Nat.exists_lt_modEq_of_infinite hx n.succ_pos with ⟨k, hk, l, hl, hkl, hn⟩
  set m := (l - k) / (n + 1)
  have : (n + 1) * m = l - k := by
    apply Nat.mul_div_cancel'
    exact (Nat.modEq_iff_dvd' hkl.le).1 hn
  refine ⟨f^[k] x, hk, m, ?_, ?_⟩
  · intro hm
    rw [hm]; rw [mul_zero]; rw [eq_comm]; rw [tsub_eq_zero_iff_le] at this
    exact this.not_gt hkl
  · rwa [← iterate_mul, this, ← iterate_add_apply, tsub_add_cancel_of_le]
    exact hkl.le

中文:
定理 iterate
  条件: (hf : 余nservative f μ) (n : 自然数)
  结论: 余nservative f^[n] μ
  证明: by
  -- Discharge the trivial case `n = 0`
  rcases n with - | n
  · exact Conservative.id μ
  refine ⟨hf.1.iterate _, fun s hs hs0 => ?_⟩
  rcases (hf.frequently_ae_mem_and_frequently_image_mem hs.nullMeasurableSet hs0).exists
    with ⟨x, _, hx⟩
  /- We take a point `x ∈ s` such that `f^[k] x ∈ s` for infinitely many values of `k`,
    then we choose two of these values `k < l` such that `k ≡ l [MOD (n + 1)]`.
    Then `f^[k] x ∈ s` and `f^[n + 1]^[(l - k) / (n + 1)] (f^[k] x) = f^[l] x ∈ s`. -/
  rw [Nat.frequently_atTop_iff_infinite] at hx
  rcases Nat.exists_lt_modEq_of_infinite hx n.succ_pos with ⟨k, hk, l, hl, hkl, hn⟩
  set m := (l - k) / (n + 1)
  have : (n + 1) * m = l - k := by
    apply Nat.mul_div_cancel'
    exact (Nat.modEq_iff_dvd' hkl.le).1 hn
  refine ⟨f^[k] x, hk, m, ?_, ?_⟩
  · intro hm
    rw [hm]; rw [mul_zero]; rw [eq_comm]; rw [tsub_eq_zero_iff_le] at this
    exact this.not_gt hkl
  · rwa [← iterate_mul, this, ← iterate_add_apply, tsub_add_cancel_of_le]
    exact hkl.le
-/
protected theorem iterate (hf : Conservative f μ) (n : Nat) : Conservative f^[n] μ := by
  -- Discharge the trivial case `n = 0`
  rcases n with - | n
  · exact Conservative.id μ
  refine ⟨hf.1.iterate _, fun s hs hs0 => ?_⟩
  rcases (hf.frequently_ae_mem_and_frequently_image_mem hs.nullMeasurableSet hs0).exists
    with ⟨x, _, hx⟩
  /- We take a point `x ∈ s` such that `f^[k] x ∈ s` for infinitely many values of `k`,
    then we choose two of these values `k < l` such that `k ≡ l [MOD (n + 1)]`.
    Then `f^[k] x ∈ s` and `f^[n + 1]^[(l - k) / (n + 1)] (f^[k] x) = f^[l] x ∈ s`. -/
  rw [Nat.frequently_atTop_iff_infinite] at hx
  rcases Nat.exists_lt_modEq_of_infinite hx n.succ_pos with ⟨k, hk, l, hl, hkl, hn⟩
  set m := (l - k) / (n + 1)
  have : (n + 1) * m = l - k := by
    apply Nat.mul_div_cancel'
    exact (Nat.modEq_iff_dvd' hkl.le).1 hn
  refine ⟨f^[k] x, hk, m, ?_, ?_⟩
  · intro hm
    rw [hm]; rw [mul_zero]; rw [eq_comm]; rw [tsub_eq_zero_iff_le] at this
    exact this.not_gt hkl
  · rwa [← iterate_mul, this, ← iterate_add_apply, tsub_add_cancel_of_le]
    exact hkl.le

end Conservative

end MeasureTheory
