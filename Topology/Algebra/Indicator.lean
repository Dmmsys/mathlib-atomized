/-
Copyright (c) 2024 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Clopen

/-!
# Continuity of indicator functions
-/

public section

open Set
open scoped Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α -> β} {s : Set α} [One β]

@[to_additive]
/--
lemma `continuous_mulIndicator` / 引理 `continuous_mulIndicator`

English:
lemma continuous_mulIndicator
  given: (hs : forall a in frontier s, f a = 1) (hf : ContinuousOn f (closure s))
  proof: by
  classical exact continuous_piecewise hs hf continuousOn_const

@[to_additive]

中文:
引理 continuous_mulIndicator
  条件: (hs : 对任意 a in frontier s, f a = 1) (hf : ContinuousOn f (closure s))
  证明: by
  classical exact continuous_piecewise hs hf continuousOn_const

@[to_additive]

Depends on / 依赖: classical, continuousOn_const, continuous_piecewise
-/
lemma continuous_mulIndicator (hs : forall a in frontier s, f a = 1) (hf : ContinuousOn f (closure s)) :
    Continuous (mulIndicator s f) := by
  classical exact continuous_piecewise hs hf continuousOn_const

@[to_additive]
/--
lemma `Continuous.mulIndicator` / 引理 `Continuous.mulIndicator`

English:
lemma Continuous.mulIndicator
  given: (hs : forall a in frontier s, f a = 1) (hf : Continuous f)
  proof: by
  classical exact hf.piecewise hs continuous_const

@[to_additive]

中文:
引理 连续.mulIndicator
  条件: (hs : 对任意 a in frontier s, f a = 1) (hf : 连续 f)
  证明: by
  classical exact hf.piecewise hs continuous_const

@[to_additive]
-/
protected lemma Continuous.mulIndicator (hs : forall a in frontier s, f a = 1) (hf : Continuous f) :
    Continuous (mulIndicator s f) := by
  classical exact hf.piecewise hs continuous_const

@[to_additive]
/--
theorem `ContinuousOn.continuousAt_mulIndicator` / 定理 `ContinuousOn.continuousAt_mulIndicator`

English:
theorem ContinuousOn.continuousAt_mulIndicator
  statement: (hf : ContinuousOn f (interior s)) {x : α}
  proof: by
  rw [← Set.mem_compl_iff]; rw [compl_frontier_eq_union_interior] at hx
  obtain h | h := hx
  · have hs : interior s in 𝓝 x := mem_interior_iff_mem_nhds.mp (by rwa [interior_interior])
exact ContinuousAt.congr (hf.continuousAt hs) Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨interior s, hs, Set.eqOn_mulIndicator.symm.mono interior_subset⟩
· exact ContinuousAt.congr continuousAt_const Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨sᶜ, mem_interior_iff_mem_nhds.mp h, Set.eqOn_mulIndicator'.symm⟩

@[to_additive]

中文:
定理 ContinuousOn.continuousAt_mulIndicator
  结论: (hf : ContinuousOn f (interior s)) {x : α}
  证明: by
  rw [← Set.mem_compl_iff]; rw [compl_frontier_eq_union_interior] at hx
  obtain h | h := hx
  · have hs : interior s in 𝓝 x := mem_interior_iff_mem_nhds.mp (by rwa [interior_interior])
exact ContinuousAt.congr (hf.continuousAt hs) Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨interior s, hs, Set.eqOn_mulIndicator.symm.mono interior_subset⟩
· exact ContinuousAt.congr continuousAt_const Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨sᶜ, mem_interior_iff_mem_nhds.mp h, Set.eqOn_mulIndicator'.symm⟩

@[to_additive]

Depends on / 依赖: ContinuousAt, ContinuousAt.congr, Filter, Filter.eventuallyEq_iff_exists_mem.mpr, Set.eqOn_mulIndicator, Set.eqOn_mulIndicator.symm.mono, Set.mem_compl_iff, compl_frontier_eq_union_interior, continuousAt, continuousAt_const, eqOn_mulIndicator, eventuallyEq_iff_exists_mem, hf.continuousAt, interior, interior_interior, interior_subset, mem_compl_iff, mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds.mp
-/
theorem ContinuousOn.continuousAt_mulIndicator (hf : ContinuousOn f (interior s)) {x : α}
    (hx : x ∉ frontier s) :
    ContinuousAt (s.mulIndicator f) x := by
  rw [← Set.mem_compl_iff]; rw [compl_frontier_eq_union_interior] at hx
  obtain h | h := hx
  · have hs : interior s in 𝓝 x := mem_interior_iff_mem_nhds.mp (by rwa [interior_interior])
exact ContinuousAt.congr (hf.continuousAt hs) Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨interior s, hs, Set.eqOn_mulIndicator.symm.mono interior_subset⟩
· exact ContinuousAt.congr continuousAt_const Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨sᶜ, mem_interior_iff_mem_nhds.mp h, Set.eqOn_mulIndicator'.symm⟩

@[to_additive]
/--
lemma `IsClopen.continuous_mulIndicator` / 引理 `IsClopen.continuous_mulIndicator`

English:
lemma IsClopen.continuous_mulIndicator
  given: (hs : IsClopen s) (hf : Continuous f)
  proof: hf.mulIndicator (by simp [isClopen_iff_frontier_eq_empty.mp hs])

中文:
引理 IsClopen.continuous_mulIndicator
  条件: (hs : IsClopen s) (hf : 连续 f)
  证明: hf.mulIndicator (by simp [isClopen_iff_frontier_eq_empty.mp hs])

Depends on / 依赖: hf.mulIndicator, isClopen_iff_frontier_eq_empty, isClopen_iff_frontier_eq_empty.mp, mulIndicator
-/
lemma IsClopen.continuous_mulIndicator (hs : IsClopen s) (hf : Continuous f) :
    Continuous (s.mulIndicator f) :=
  hf.mulIndicator (by simp [isClopen_iff_frontier_eq_empty.mp hs])
