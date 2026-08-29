/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Indexed product of sets with unique differentiability property

In this file we prove that the indexed product
of a family sets with unique differentiability property
has the same property, see `UniqueDiffOn.pi` and `UniqueDiffOn.univ_pi`.
-/

public section

open Filter Set
open scoped Topology

section Semiring

variable {𝕜 : Type*} [Semiring 𝕜]
  {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)]
  [forall i, TopologicalSpace (E i)] [forall i, ContinuousAdd (E i)] [forall i, ContinuousConstSMul 𝕜 (E i)]
  {s : forall i, Set (E i)} {x : forall i, E i}

/--
theorem `mapsTo_tangentConeAt_pi` / 定理 `mapsTo_tangentConeAt_pi`

English:
theorem mapsTo_tangentConeAt_pi
  given: [DecidableEq ι] {i : ι} (hi : forall j != i, x j in closure (s j))
  proof: by
  rw [← tangentConeAt_closure (s := .pi _ _)]
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  apply mem_tangentConeAt_of_seq l c (fun n => Pi.single i (d n))
  · rw [tendsto_pi_nhds]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, ten

中文:
定理 mapsTo_tangentConeAt_pi
  条件: [DecidableEq ι] {i : ι} (hi : 对任意 j != i, x j in closure (s j))
  证明: by
  rw [← tangentConeAt_closure (s := .pi _ _)]
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  apply mem_tangentConeAt_of_seq l c (fun n => Pi.single i (d n))
  · rw [tendsto_pi_nhds]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, ten

Depends on / 依赖: Pi.single, closure_pi_set, eq_or_ne, exists_fun_of_mem_tangentConeAt, hds.mono, mem_tangentConeAt_of_seq, mem_univ_pi, single, subset_closure, tangentConeAt_closure, tendsto_const_nhds, tendsto_pi_nhds
-/
theorem mapsTo_tangentConeAt_pi [DecidableEq ι] {i : ι} (hi : forall j != i, x j in closure (s j)) :
    MapsTo (Pi.single i) (tangentConeAt 𝕜 (s i) (x i)) (tangentConeAt 𝕜 (Set.pi univ s) x) := by
  rw [← tangentConeAt_closure (s := .pi _ _)]
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  apply mem_tangentConeAt_of_seq l c (fun n => Pi.single i (d n))
  · rw [tendsto_pi_nhds]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, tendsto_const_nhds]
  · refine hds.mono fun n hn => ?_
    rw [closure_pi_set]; rw [mem_univ_pi]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, subset_closure hn]
  · rw [tendsto_pi_nhds]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, tendsto_const_nhds]

/--
theorem `UniqueDiffWithinAt.univ_pi` / 定理 `UniqueDiffWithinAt.univ_pi`

English:
theorem UniqueDiffWithinAt.univ_pi
  statement: {s : forall i, Set (E i)} {x : forall i, E i}
  proof: by
  classical
  simp only [uniqueDiffWithinAt_iff, closure_pi_set] at h ⊢
refine ⟨.of_closure (dense_pi univ fun i _ => (h i).1).closure.mono ?_, fun i _ => (h i).2⟩
  simp only [closure_pi_set, ← Submodule.closure_coe_iSup_map_single, Submodule.map_span]
  gcongr
  refine iSup_le fun i => ?_
  gco

中文:
定理 UniqueDiffWithinAt.univ_pi
  结论: {s : 对任意 i, Set (E i)} {x : 对任意 i, E i}
  证明: by
  classical
  simp only [uniqueDiffWithinAt_iff, closure_pi_set] at h ⊢
refine ⟨.of_closure (dense_pi univ fun i _ => (h i).1).closure.mono ?_, fun i _ => (h i).2⟩
  simp only [closure_pi_set, ← Submodule.closure_coe_iSup_map_single, Submodule.map_span]
  gcongr
  refine iSup_le fun i => ?_
  gco

Depends on / 依赖: Submodule, Submodule.closure_coe_iSup_map_single, Submodule.map_span, classical, closure, closure.mono, closure_coe_iSup_map_single, closure_pi_set, dense_pi, iSup_le, image_subset, map_span, mapsTo_tangentConeAt_pi, of_closure, uniqueDiffWithinAt_iff
-/
theorem UniqueDiffWithinAt.univ_pi {s : forall i, Set (E i)} {x : forall i, E i}
    (h : forall i, UniqueDiffWithinAt 𝕜 (s i) (x i)) : UniqueDiffWithinAt 𝕜 (Set.pi univ s) x := by
  classical
  simp only [uniqueDiffWithinAt_iff, closure_pi_set] at h ⊢
refine ⟨.of_closure (dense_pi univ fun i _ => (h i).1).closure.mono ?_, fun i _ => (h i).2⟩
  simp only [closure_pi_set, ← Submodule.closure_coe_iSup_map_single, Submodule.map_span]
  gcongr
  refine iSup_le fun i => ?_
  gcongr
.image_subset exact mapsTo_tangentConeAt_pi (fun j _ => (h j).2)

/--
theorem `UniqueDiffOn.univ_pi` / 定理 `UniqueDiffOn.univ_pi`

English:
theorem UniqueDiffOn.univ_pi
  given: {s : forall i, Set (E i)} (h : forall i, UniqueDiffOn 𝕜 (s i))
  proof: fun _x hx => .univ_pi fun i => h i _ hx i (mem_univ i)

中文:
定理 UniqueDiffOn.univ_pi
  条件: {s : 对任意 i, Set (E i)} (h : 对任意 i, UniqueDiffOn 𝕜 (s i))
  证明: fun _x hx => .univ_pi fun i => h i _ hx i (mem_univ i)

Depends on / 依赖: mem_univ, univ_pi
-/
theorem UniqueDiffOn.univ_pi {s : forall i, Set (E i)} (h : forall i, UniqueDiffOn 𝕜 (s i)) :
    UniqueDiffOn 𝕜 (Set.pi univ s) :=
fun _x hx => .univ_pi fun i => h i _ hx i (mem_univ i)

end Semiring

variable {𝕜 : Type*} [DivisionSemiring 𝕜]
  {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)]
  [TopologicalSpace 𝕜] [(𝓝[!=] (0 : 𝕜)).NeBot]
  [forall i, TopologicalSpace (E i)] [forall i, ContinuousAdd (E i)] [forall i, ContinuousSMul 𝕜 (E i)]
  {s : forall i, Set (E i)} {x : forall i, E i} {I : Set ι}

/--
theorem `UniqueDiffWithinAt.pi` / 定理 `UniqueDiffWithinAt.pi`

English:
theorem UniqueDiffWithinAt.pi
  given: (h : forall i in I, UniqueDiffWithinAt 𝕜 (s i) (x i))
  proof: by
  classical
  rw [← Set.univ_pi_piecewise_univ]
  refine UniqueDiffWithinAt.univ_pi fun i => ?_
  by_cases hi : i in I <;> simp [*, uniqueDiffWithinAt_univ]

中文:
定理 UniqueDiffWithinAt.pi
  条件: (h : 对任意 i in I, UniqueDiffWithinAt 𝕜 (s i) (x i))
  证明: by
  classical
  rw [← Set.univ_pi_piecewise_univ]
  refine UniqueDiffWithinAt.univ_pi fun i => ?_
  by_cases hi : i in I <;> simp [*, uniqueDiffWithinAt_univ]

Depends on / 依赖: Set.univ_pi_piecewise_univ, UniqueDiffWithinAt, UniqueDiffWithinAt.univ_pi, classical, uniqueDiffWithinAt_univ, univ_pi, univ_pi_piecewise_univ
-/
theorem UniqueDiffWithinAt.pi (h : forall i in I, UniqueDiffWithinAt 𝕜 (s i) (x i)) :
    UniqueDiffWithinAt 𝕜 (Set.pi I s) x := by
  classical
  rw [← Set.univ_pi_piecewise_univ]
  refine UniqueDiffWithinAt.univ_pi fun i => ?_
  by_cases hi : i in I <;> simp [*, uniqueDiffWithinAt_univ]

/--
theorem `UniqueDiffOn.pi` / 定理 `UniqueDiffOn.pi`

English:
theorem UniqueDiffOn.pi
  given: (h : forall i in I, UniqueDiffOn 𝕜 (s i))
  statement: UniqueDiffOn 𝕜 (Set.pi I s)
  proof: fun x hx => UniqueDiffWithinAt.pi fun i hi => h i hi (x i) (hx i hi)

中文:
定理 UniqueDiffOn.pi
  条件: (h : 对任意 i in I, UniqueDiffOn 𝕜 (s i))
  结论: UniqueDiffOn 𝕜 (Set.pi I s)
  证明: fun x hx => UniqueDiffWithinAt.pi fun i hi => h i hi (x i) (hx i hi)

Depends on / 依赖: UniqueDiffWithinAt, UniqueDiffWithinAt.pi
-/
theorem UniqueDiffOn.pi (h : forall i in I, UniqueDiffOn 𝕜 (s i)) : UniqueDiffOn 𝕜 (Set.pi I s) :=
  fun x hx => UniqueDiffWithinAt.pi fun i hi => h i hi (x i) (hx i hi)
