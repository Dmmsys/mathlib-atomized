/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.Filter.Pointwise
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Tangent cone

In this file, we define two predicates `UniqueDiffWithinAt 𝕜 s x` and `UniqueDiffOn 𝕜 s`
ensuring that, if a function has two derivatives, then they have to coincide. As a direct
definition of this fact (quantifying on all target types and all functions) would depend on
universes, we use a more intrinsic definition: if all the possible tangent directions to the set
`s` at the point `x` span a dense subset of the whole subset, it is easy to check that the
derivative has to be unique.

Therefore, we introduce the set of all tangent directions, named `tangentConeAt`,
and express `UniqueDiffWithinAt` and `UniqueDiffOn` in terms of it.
One should however think of this definition as an implementation detail: the only reason to
introduce the predicates `UniqueDiffWithinAt` and `UniqueDiffOn` is to ensure the uniqueness
of the derivative. This is why their names reflect their uses, and not how they are defined.

## Implementation details

Note that this file is imported by `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. Hence, derivatives
are not defined yet. The property of uniqueness of the derivative is therefore proved in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`, but based on the properties of the tangent cone we
prove here.
-/

@[expose] public section

open Filter Set Metric
open scoped Topology Pointwise

universe u v
variable (R : Type u) {E : Type v}

section TangentConeAt

variable [AddCommGroup E] [SMul R E] [TopologicalSpace E] {s : Set E} {x y : E}

/-- The set of all tangent directions to the set `s` at the point `x`.

A point `y` belongs to the tangent cone of `s` at `x` iff
there exist a family of scalars `c n`, a family of vectors `d n`,
and a nontrivial filter in the index type such that

- `d n → 0` along the filter;
- `x + d n ∈ s` eventually along the filter;
- `c n • d n → y` along the filter,

The actual definition is given in terms of cluster points of a filter,
see `mem_tangentConeAt_of_seq` and `exists_fun_of_mem_tangentConeAt`
for the two implications unfolding this definition in more convenient way.

In a space with first countable topology,
one can assume that the index type is `ℕ` and the filter is `atTop`,
but the definition we use is more useful without that assumption.
-/
irreducible_def tangentConeAt (s : Set E) (x : E) : Set E :=
  {y : E | ClusterPt y ((⊤ : Filter R) • 𝓝[(x + ·) ⁻¹' s] 0)}

variable {R}

/--
theorem `mem_tangentConeAt_of_frequently` / 定理 `mem_tangentConeAt_of_frequently`

English:
theorem mem_tangentConeAt_of_frequently
  statement: {α : Type*} (l : Filter α) (c : α -> R) (d : α -> E)
  proof: by
  suffices Tendsto (fun n => c n • d n) (l ⊓ 𝓟 {y | x + d y in s}) (⊤ • 𝓝[(x + ·) ⁻¹' s] 0) by
    rw [frequently_iff_neBot] at hds
    rw [tangentConeAt_def]
    exact ClusterPt.mono (hcd.mono_left inf_le_left).mapClusterPt this
  rw [← map₂_smul]; rw [← map_prod_eq_map₂]
  refine tendsto_map.co

中文:
定理 mem_tangentConeAt_of_frequently
  结论: {α : 类型} (l : 滤子 α) (c : α -> R) (d : α -> E)
  证明: by
  suffices Tendsto (fun n => c n • d n) (l ⊓ 𝓟 {y | x + d y in s}) (⊤ • 𝓝[(x + ·) ⁻¹' s] 0) by
    rw [frequently_iff_neBot] at hds
    rw [tangentConeAt_def]
    exact ClusterPt.mono (hcd.mono_left inf_le_left).mapClusterPt this
  rw [← map₂_smul]; rw [← map_prod_eq_map₂]
  refine tendsto_map.co

Depends on / 依赖: ClusterPt, ClusterPt.mono, Tendsto, eventually_inf_principal, frequently_iff_neBot, hcd.mono_left, inf_le_left, mapClusterPt, mono_left, prodMk, tangentConeAt_def, tendsto_map, tendsto_map.comp, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mpr, tendsto_top, tendsto_top.prodMk
-/
theorem mem_tangentConeAt_of_frequently {α : Type*} (l : Filter α) (c : α -> R) (d : α -> E)
    (hd₀ : Tendsto d l (𝓝 0)) (hds : existsᶠ n in l, x + d n in s)
    (hcd : Tendsto (fun n => c n • d n) l (𝓝 y)) : y in tangentConeAt R s x := by
  suffices Tendsto (fun n => c n • d n) (l ⊓ 𝓟 {y | x + d y in s}) (⊤ • 𝓝[(x + ·) ⁻¹' s] 0) by
    rw [frequently_iff_neBot] at hds
    rw [tangentConeAt_def]
    exact ClusterPt.mono (hcd.mono_left inf_le_left).mapClusterPt this
  rw [← map₂_smul]; rw [← map_prod_eq_map₂]
  refine tendsto_map.comp (tendsto_top.prodMk (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩))
  · exact hd₀.mono_left inf_le_left
  · simp [eventually_inf_principal]

/--
theorem `mem_tangentConeAt_of_seq` / 定理 `mem_tangentConeAt_of_seq`

English:
theorem mem_tangentConeAt_of_seq
  statement: {α : Type*} (l : Filter α) [l.NeBot] (c : α -> R) (d : α -> E)
  proof: mem_tangentConeAt_of_frequently l c d hd₀ hds.frequently hcd

中文:
定理 mem_tangentConeAt_of_seq
  结论: {α : 类型} (l : 滤子 α) [l.NeBot] (c : α -> R) (d : α -> E)
  证明: mem_tangentConeAt_of_frequently l c d hd₀ hds.frequently hcd

Depends on / 依赖: frequently, hds.frequently, mem_tangentConeAt_of_frequently
-/
theorem mem_tangentConeAt_of_seq {α : Type*} (l : Filter α) [l.NeBot] (c : α -> R) (d : α -> E)
    (hd₀ : Tendsto d l (𝓝 0)) (hds : forallᶠ n in l, x + d n in s)
    (hcd : Tendsto (fun n => c n • d n) l (𝓝 y)) : y in tangentConeAt R s x :=
  mem_tangentConeAt_of_frequently l c d hd₀ hds.frequently hcd

/--
theorem `exists_fun_of_mem_tangentConeAt` / 定理 `exists_fun_of_mem_tangentConeAt`

English:
theorem exists_fun_of_mem_tangentConeAt
  given: (h : y in tangentConeAt R s x)
  proof: by
  rw [tangentConeAt]; rw [mem_ofPred]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [ClusterPt]; rw [← neBot_inf_comap_iff_map'] at h
  refine ⟨R × E, _, h, Prod.fst, Prod.snd, ?_, ?_, ?_⟩
· refine (tendsto_snd (f := ⊤)).mono_left inf_le_right.trans ?_
    gcongr
    apply nhdsWithin_le_nhds
  ·

中文:
定理 存在_fun_of_mem_tangentConeAt
  条件: (h : y in tangentConeAt R s x)
  证明: by
  rw [tangentConeAt]; rw [mem_ofPred]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [ClusterPt]; rw [← neBot_inf_comap_iff_map'] at h
  refine ⟨R × E, _, h, Prod.fst, Prod.snd, ?_, ?_, ?_⟩
· refine (tendsto_snd (f := ⊤)).mono_left inf_le_right.trans ?_
    gcongr
    apply nhdsWithin_le_nhds
  ·

Depends on / 依赖: ClusterPt, Prod.fst, Prod.snd, contextual, eventually_comap, eventually_mem_nhdsWithin, filter_mono, filter_upwards, inf_le_left, inf_le_right, inf_le_right.trans, mem_ofPred, mono_left, neBot_inf_comap_iff_map, nhdsWithin_le_nhds, tangentConeAt, tendsto_comap, tendsto_comap.mono_left, tendsto_snd, top_prod
-/
theorem exists_fun_of_mem_tangentConeAt (h : y in tangentConeAt R s x) :
    exists (α : Type (max u v)) (l : Filter α) (_hl : l.NeBot) (c : α -> R) (d : α -> E),
      Tendsto d l (𝓝 0) ∧ (forallᶠ n in l, x + d n in s) ∧ Tendsto (fun n => c n • d n) l (𝓝 y) := by
  rw [tangentConeAt]; rw [mem_ofPred]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [ClusterPt]; rw [← neBot_inf_comap_iff_map'] at h
  refine ⟨R × E, _, h, Prod.fst, Prod.snd, ?_, ?_, ?_⟩
· refine (tendsto_snd (f := ⊤)).mono_left inf_le_right.trans ?_
    gcongr
    apply nhdsWithin_le_nhds
  · refine .filter_mono inf_le_right ?_
    rw [top_prod]; rw [eventually_comap]
    filter_upwards [eventually_mem_nhdsWithin]
    simp +contextual
  · exact tendsto_comap.mono_left inf_le_left

end TangentConeAt

/--
Definition of `posTangentConeAt` / `posTangentConeAt` 的定义

English:
abbreviation posTangentConeAt
  signature: [AddCommGroup E] [Module Real E] [TopologicalSpace E] (s : Set E) (x : E)
  body: tangentConeAt NNReal s x

中文:
缩写 posTangentConeAt
  签名: [加法交换群 E] [模 实数 E] [拓扑空间 E] (s : 集合 E) (x : E)
  定义体: tangentConeAt NNReal s x

Depends on / 依赖: NNReal, tangentConeAt
-/
abbrev posTangentConeAt [AddCommGroup E] [Module Real E] [TopologicalSpace E] (s : Set E) (x : E) :
    Set E :=
  tangentConeAt NNReal s x

variable [Semiring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `UniqueDiffWithinAt.eq` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.
To avoid pathologies in dimension 0, we also require that `x` belongs to the closure of `s` (which
is automatic when `E` is not `0`-dimensional). -/
@[mk_iff]
/--
Definition of `UniqueDiffWithinAt` / `UniqueDiffWithinAt` 的定义

English:
structure UniqueDiffWithinAt
  parameters: (s : Set E) (x : E)
  axioms and operations (2):
    - dense_tangentConeAt : Dense (Submodule.span R (tangentConeAt R s x) : Set E)
    - mem_closure : x in closure s

中文:
结构 UniqueDiffWithinAt
  参数: (s : 集合 E) (x : E)
  公理与运算 (2 个):
    - dense_tangentConeAt : 稠密 (子模.span R (tangentConeAt R s x) : 集合 E)
    - mem_closure : x in closure s
-/
structure UniqueDiffWithinAt (s : Set E) (x : E) : Prop where
  dense_tangentConeAt : Dense (Submodule.span R (tangentConeAt R s x) : Set E)
  mem_closure : x in closure s

/--
Definition of `UniqueDiffOn` / `UniqueDiffOn` 的定义

English:
definition UniqueDiffOn
  signature: (s : Set E)
  body: forall x in s, UniqueDiffWithinAt R s x

中文:
定义 UniqueDiffOn
  签名: (s : 集合 E)
  定义体: forall x in s, UniqueDiffWithinAt R s x

Depends on / 依赖: UniqueDiffWithinAt
-/
def UniqueDiffOn (s : Set E) : Prop :=
  forall x in s, UniqueDiffWithinAt R s x

variable {R} in
/--
theorem `UniqueDiffOn.uniqueDiffWithinAt` / 定理 `UniqueDiffOn.uniqueDiffWithinAt`

English:
theorem UniqueDiffOn.uniqueDiffWithinAt
  given: {s : Set E} {x} (hs : UniqueDiffOn R s) (h : x in s)
  proof: hs x h

中文:
定理 UniqueDiffOn.uniqueDiffWithinAt
  条件: {s : 集合 E} {x} (hs : UniqueDiffOn R s) (h : x in s)
  证明: hs x h
-/
theorem UniqueDiffOn.uniqueDiffWithinAt {s : Set E} {x} (hs : UniqueDiffOn R s) (h : x in s) :
    UniqueDiffWithinAt R s x :=
  hs x h
