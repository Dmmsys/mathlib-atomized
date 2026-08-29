/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.Calculus.TangentCone.Basic

/-!
# Product of sets with unique differentiability property

In this file we prove that the product of two sets with unique differentiability property
has the same property, see `UniqueDiffOn.prod`.
-/

public section

open Filter Set
open scoped Topology

variable {𝕜 E F : Type*} [Semiring 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousConstSMul 𝕜 F]
  {x : E} {s : Set E} {y : F} {t : Set F}

/--
theorem `subset_tangentConeAt_prod_left` / 定理 `subset_tangentConeAt_prod_left`

English:
theorem subset_tangentConeAt_prod_left
  given: (ht : y in closure t)
  proof: by
  rw [← tangentConeAt_closure (s := s ×ˢ t)]; rw [closure_prod_eq]
  rintro _ ⟨z, hz, rfl⟩
  rcases exists_fun_of_mem_tangentConeAt hz with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  refine mem_tangentConeAt_of_seq l c (fun n => (d n, 0)) (hd₀.prodMk_nhds tendsto_const_nhds)
    (hds.mono fun n hn => by simp [ht, subset_closure hn]) ?_
  simpa using hcd.prodMk_nhds tendsto_const_nhds

中文:
定理 subset_tangentConeAt_prod_left
  条件: (ht : y in closure t)
  证明: by
  rw [← tangentConeAt_closure (s := s ×ˢ t)]; rw [closure_prod_eq]
  rintro _ ⟨z, hz, rfl⟩
  rcases exists_fun_of_mem_tangentConeAt hz with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  refine mem_tangentConeAt_of_seq l c (fun n => (d n, 0)) (hd₀.prodMk_nhds tendsto_const_nhds)
    (hds.mono fun n hn => by simp [ht, subset_closure hn]) ?_
  simpa using hcd.prodMk_nhds tendsto_const_nhds

Depends on / 依赖: closure_prod_eq, exists_fun_of_mem_tangentConeAt, hcd.prodMk_nhds, hds.mono, mem_tangentConeAt_of_seq, prodMk_nhds, subset_closure, tangentConeAt_closure, tendsto_const_nhds
-/
theorem subset_tangentConeAt_prod_left (ht : y in closure t) :
    LinearMap.inl 𝕜 E F '' tangentConeAt 𝕜 s x subseteq tangentConeAt 𝕜 (s ×ˢ t) (x, y) := by
  rw [← tangentConeAt_closure (s := s ×ˢ t)]; rw [closure_prod_eq]
  rintro _ ⟨z, hz, rfl⟩
  rcases exists_fun_of_mem_tangentConeAt hz with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  refine mem_tangentConeAt_of_seq l c (fun n => (d n, 0)) (hd₀.prodMk_nhds tendsto_const_nhds)
    (hds.mono fun n hn => by simp [ht, subset_closure hn]) ?_
  simpa using hcd.prodMk_nhds tendsto_const_nhds

/--
theorem `subset_tangentConeAt_prod_right` / 定理 `subset_tangentConeAt_prod_right`

English:
theorem subset_tangentConeAt_prod_right
  given: (hs : x in closure s)
  proof: by
  rw [← tangentConeAt_closure (s := s ×ˢ t)]; rw [closure_prod_eq]
  rintro _ ⟨z, hz, rfl⟩
  rcases exists_fun_of_mem_tangentConeAt hz with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  refine mem_tangentConeAt_of_seq l c (fun n => (0, d n)) (tendsto_const_nhds.prodMk_nhds hd₀)
    (hds.mono fun n hn => by simp [hs, subset_closure hn]) ?_
  simpa using tendsto_const_nhds.prodMk_nhds hcd

中文:
定理 subset_tangentConeAt_prod_right
  条件: (hs : x in closure s)
  证明: by
  rw [← tangentConeAt_closure (s := s ×ˢ t)]; rw [closure_prod_eq]
  rintro _ ⟨z, hz, rfl⟩
  rcases exists_fun_of_mem_tangentConeAt hz with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  refine mem_tangentConeAt_of_seq l c (fun n => (0, d n)) (tendsto_const_nhds.prodMk_nhds hd₀)
    (hds.mono fun n hn => by simp [hs, subset_closure hn]) ?_
  simpa using tendsto_const_nhds.prodMk_nhds hcd

Depends on / 依赖: closure_prod_eq, exists_fun_of_mem_tangentConeAt, hds.mono, mem_tangentConeAt_of_seq, prodMk_nhds, subset_closure, tangentConeAt_closure, tendsto_const_nhds, tendsto_const_nhds.prodMk_nhds
-/
theorem subset_tangentConeAt_prod_right (hs : x in closure s) :
    LinearMap.inr 𝕜 E F '' tangentConeAt 𝕜 t y subseteq tangentConeAt 𝕜 (s ×ˢ t) (x, y) := by
  rw [← tangentConeAt_closure (s := s ×ˢ t)]; rw [closure_prod_eq]
  rintro _ ⟨z, hz, rfl⟩
  rcases exists_fun_of_mem_tangentConeAt hz with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  refine mem_tangentConeAt_of_seq l c (fun n => (0, d n)) (tendsto_const_nhds.prodMk_nhds hd₀)
    (hds.mono fun n hn => by simp [hs, subset_closure hn]) ?_
  simpa using tendsto_const_nhds.prodMk_nhds hcd

/--
theorem `UniqueDiffWithinAt.prod` / 定理 `UniqueDiffWithinAt.prod`

English:
theorem UniqueDiffWithinAt.prod
  statement: (hs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  rw [uniqueDiffWithinAt_iff] at hs ht ⊢
  rw [closure_prod_eq]
  refine ⟨?_, hs.2, ht.2⟩
  have : _ <= Submodule.span 𝕜 (tangentConeAt 𝕜 (s ×ˢ t) (x, y)) := Submodule.span_mono
    (union_subset (subset_tangentConeAt_prod_left ht.2) (subset_tangentConeAt_prod_right hs.2))
  rw [LinearMap.span_inl_union_inr]; rw [SetLike.le_def] at this
  exact (hs.1.prod ht.1).mono this

中文:
定理 UniqueDiffWithinAt.乘积
  结论: (hs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  rw [uniqueDiffWithinAt_iff] at hs ht ⊢
  rw [closure_prod_eq]
  refine ⟨?_, hs.2, ht.2⟩
  have : _ <= Submodule.span 𝕜 (tangentConeAt 𝕜 (s ×ˢ t) (x, y)) := Submodule.span_mono
    (union_subset (subset_tangentConeAt_prod_left ht.2) (subset_tangentConeAt_prod_right hs.2))
  rw [LinearMap.span_inl_union_inr]; rw [SetLike.le_def] at this
  exact (hs.1.prod ht.1).mono this

Depends on / 依赖: LinearMap, LinearMap.span_inl_union_inr, SetLike, SetLike.le_def, Submodule, Submodule.span, Submodule.span_mono, closure_prod_eq, le_def, span_inl_union_inr, span_mono, subset_tangentConeAt_prod_left, subset_tangentConeAt_prod_right, tangentConeAt, union_subset, uniqueDiffWithinAt_iff
-/
theorem UniqueDiffWithinAt.prod (hs : UniqueDiffWithinAt 𝕜 s x)
    (ht : UniqueDiffWithinAt 𝕜 t y) : UniqueDiffWithinAt 𝕜 (s ×ˢ t) (x, y) := by
  rw [uniqueDiffWithinAt_iff] at hs ht ⊢
  rw [closure_prod_eq]
  refine ⟨?_, hs.2, ht.2⟩
  have : _ <= Submodule.span 𝕜 (tangentConeAt 𝕜 (s ×ˢ t) (x, y)) := Submodule.span_mono
    (union_subset (subset_tangentConeAt_prod_left ht.2) (subset_tangentConeAt_prod_right hs.2))
  rw [LinearMap.span_inl_union_inr]; rw [SetLike.le_def] at this
  exact (hs.1.prod ht.1).mono this

/--
theorem `UniqueDiffOn.prod` / 定理 `UniqueDiffOn.prod`

English:
theorem UniqueDiffOn.prod
  given: (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t)
  proof: fun ⟨x, y⟩ h => UniqueDiffWithinAt.prod (hs x h.1) (ht y h.2)

中文:
定理 UniqueDiffOn.乘积
  条件: (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t)
  证明: fun ⟨x, y⟩ h => UniqueDiffWithinAt.prod (hs x h.1) (ht y h.2)

Depends on / 依赖: UniqueDiffWithinAt, UniqueDiffWithinAt.prod
-/
theorem UniqueDiffOn.prod (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) :
    UniqueDiffOn 𝕜 (s ×ˢ t) :=
  fun ⟨x, y⟩ h => UniqueDiffWithinAt.prod (hs x h.1) (ht y h.2)
