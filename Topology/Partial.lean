/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.Partial
public import Mathlib.Topology.Neighborhoods

/-!
# Partial functions and topological spaces

In this file we prove properties of `Filter.PTendsto` etc. in topological spaces. We also introduce
`PContinuous`, a version of `Continuous` for partially defined functions.
-/

@[expose] public section


open Filter

open Topology

variable {X Y : Type*} [TopologicalSpace X]

/--
theorem `rtendsto_nhds` / 定理 `rtendsto_nhds`

English:
theorem rtendsto_nhds
  given: {r : SetRel Y X} {l : Filter Y} {x : X}
  proof: all_mem_nhds_filter _ _ (fun _s _t => id) _

中文:
定理 rtendsto_nhds
  条件: {r : SetRel Y X} {l : 滤子 Y} {x : X}
  证明: all_mem_nhds_filter _ _ (fun _s _t => id) _

Depends on / 依赖: all_mem_nhds_filter
-/
theorem rtendsto_nhds {r : SetRel Y X} {l : Filter Y} {x : X} :
    RTendsto r l (𝓝 x) ↔ forall s, IsOpen s -> x in s -> r.core s in l :=
  all_mem_nhds_filter _ _ (fun _s _t => id) _

/--
theorem `rtendsto'_nhds` / 定理 `rtendsto'_nhds`

English:
theorem rtendsto'_nhds
  given: {r : SetRel Y X} {l : Filter Y} {x : X}
  proof: by
  rw [rtendsto'_def]
  apply all_mem_nhds_filter
  apply SetRel.preimage_mono

中文:
定理 rtendsto'_nhds
  条件: {r : SetRel Y X} {l : 滤子 Y} {x : X}
  证明: by
  rw [rtendsto'_def]
  apply all_mem_nhds_filter
  apply SetRel.preimage_mono

Depends on / 依赖: SetRel, SetRel.preimage_mono, _def, all_mem_nhds_filter, preimage_mono, rtendsto
-/
theorem rtendsto'_nhds {r : SetRel Y X} {l : Filter Y} {x : X} :
    RTendsto' r l (𝓝 x) ↔ forall s, IsOpen s -> x in s -> r.preimage s in l := by
  rw [rtendsto'_def]
  apply all_mem_nhds_filter
  apply SetRel.preimage_mono

/--
theorem `ptendsto_nhds` / 定理 `ptendsto_nhds`

English:
theorem ptendsto_nhds
  given: {f : Y ->. X} {l : Filter Y} {x : X}
  proof: rtendsto_nhds

中文:
定理 ptendsto_nhds
  条件: {f : Y ->. X} {l : 滤子 Y} {x : X}
  证明: rtendsto_nhds

Depends on / 依赖: rtendsto_nhds
-/
theorem ptendsto_nhds {f : Y ->. X} {l : Filter Y} {x : X} :
    PTendsto f l (𝓝 x) ↔ forall s, IsOpen s -> x in s -> f.core s in l :=
  rtendsto_nhds

/--
theorem `ptendsto'_nhds` / 定理 `ptendsto'_nhds`

English:
theorem ptendsto'_nhds
  given: {f : Y ->. X} {l : Filter Y} {x : X}
  proof: rtendsto'_nhds

中文:
定理 ptendsto'_nhds
  条件: {f : Y ->. X} {l : 滤子 Y} {x : X}
  证明: rtendsto'_nhds

Depends on / 依赖: _nhds, rtendsto
-/
theorem ptendsto'_nhds {f : Y ->. X} {l : Filter Y} {x : X} :
    PTendsto' f l (𝓝 x) ↔ forall s, IsOpen s -> x in s -> f.preimage s in l :=
  rtendsto'_nhds

/-! ### Continuity and partial functions -/


variable [TopologicalSpace Y]

/--
Definition of `PContinuous` / `PContinuous` 的定义

English:
definition PContinuous
  signature: (f : X ->. Y)
  body: forall s, IsOpen s -> IsOpen (f.preimage s)

中文:
定义 PContinuous
  签名: (f : X ->. Y)
  定义体: forall s, IsOpen s -> IsOpen (f.preimage s)

Depends on / 依赖: IsOpen, f.preimage, preimage
-/
def PContinuous (f : X ->. Y) :=
  forall s, IsOpen s -> IsOpen (f.preimage s)

/--
theorem `open_dom_of_pcontinuous` / 定理 `open_dom_of_pcontinuous`

English:
theorem open_dom_of_pcontinuous
  given: {f : X ->. Y} (h : PContinuous f)
  statement: IsOpen f.Dom
  proof: by
  rw [← PFun.preimage_univ]; exact h _ isOpen_univ

中文:
定理 open_dom_of_pcontinuous
  条件: {f : X ->. Y} (h : PContinuous f)
  结论: 是开集 f.Dom
  证明: by
  rw [← PFun.preimage_univ]; exact h _ isOpen_univ

Depends on / 依赖: PFun.preimage_univ, isOpen_univ, preimage_univ
-/
theorem open_dom_of_pcontinuous {f : X ->. Y} (h : PContinuous f) : IsOpen f.Dom := by
  rw [← PFun.preimage_univ]; exact h _ isOpen_univ

/--
theorem `pcontinuous_iff'` / 定理 `pcontinuous_iff'`

English:
theorem pcontinuous_iff'
  given: {f : X ->. Y}
  proof: by
  constructor
  · intro h x y h'
    simp only [ptendsto'_def, mem_nhds_iff]
    rintro s ⟨t, tsubs, opent, yt⟩
    exact ⟨f.preimage t, PFun.preimage_mono _ tsubs, h _ opent, ⟨y, yt, h'⟩⟩
  intro hf s os
  rw [isOpen_iff_nhds]
  rintro x ⟨y, ys, fxy⟩ t
  rw [mem_principal]
  intro (h : f.preimage s subseteq t)
  grw [← h]
  have h' : forall s in 𝓝 y, f.preimage s in 𝓝 x := by
    intro s hs
    have : PTendsto' f (𝓝 x) (𝓝 y) := hf fxy
    rw [ptendsto'_def] at this
    exact this s hs
  change f.preimage s in 𝓝 x
  apply h'
  rw [mem_nhds_iff]
  exact ⟨s, Set.Subset.refl _, os, ys⟩

中文:
定理 pcontinuous_iff'
  条件: {f : X ->. Y}
  证明: by
  constructor
  · intro h x y h'
    simp only [ptendsto'_def, mem_nhds_iff]
    rintro s ⟨t, tsubs, opent, yt⟩
    exact ⟨f.preimage t, PFun.preimage_mono _ tsubs, h _ opent, ⟨y, yt, h'⟩⟩
  intro hf s os
  rw [isOpen_iff_nhds]
  rintro x ⟨y, ys, fxy⟩ t
  rw [mem_principal]
  intro (h : f.preimage s subseteq t)
  grw [← h]
  have h' : forall s in 𝓝 y, f.preimage s in 𝓝 x := by
    intro s hs
    have : PTendsto' f (𝓝 x) (𝓝 y) := hf fxy
    rw [ptendsto'_def] at this
    exact this s hs
  change f.preimage s in 𝓝 x
  apply h'
  rw [mem_nhds_iff]
  exact ⟨s, Set.Subset.refl _, os, ys⟩

Depends on / 依赖: PFun.preimage_mono, PTendsto, _def, f.preimage, isOpen_iff_nhds, mem_nhds_iff, mem_principal, preimage, preimage_mono, ptendsto, subseteq
-/
theorem pcontinuous_iff' {f : X ->. Y} :
    PContinuous f ↔ forall {x y} (_ : y in f x), PTendsto' f (𝓝 x) (𝓝 y) := by
  constructor
  · intro h x y h'
    simp only [ptendsto'_def, mem_nhds_iff]
    rintro s ⟨t, tsubs, opent, yt⟩
    exact ⟨f.preimage t, PFun.preimage_mono _ tsubs, h _ opent, ⟨y, yt, h'⟩⟩
  intro hf s os
  rw [isOpen_iff_nhds]
  rintro x ⟨y, ys, fxy⟩ t
  rw [mem_principal]
  intro (h : f.preimage s subseteq t)
  grw [← h]
  have h' : forall s in 𝓝 y, f.preimage s in 𝓝 x := by
    intro s hs
    have : PTendsto' f (𝓝 x) (𝓝 y) := hf fxy
    rw [ptendsto'_def] at this
    exact this s hs
  change f.preimage s in 𝓝 x
  apply h'
  rw [mem_nhds_iff]
  exact ⟨s, Set.Subset.refl _, os, ys⟩

/--
theorem `continuousWithinAt_iff_ptendsto_res` / 定理 `continuousWithinAt_iff_ptendsto_res`

English:
theorem continuousWithinAt_iff_ptendsto_res
  given: (f : X -> Y) {x : X} {s : Set X}
  proof: tendsto_iff_ptendsto _ _ _ _

中文:
定理 continuousWithinAt_iff_ptendsto_res
  条件: (f : X -> Y) {x : X} {s : 集合 X}
  证明: tendsto_iff_ptendsto _ _ _ _

Depends on / 依赖: tendsto_iff_ptendsto
-/
theorem continuousWithinAt_iff_ptendsto_res (f : X -> Y) {x : X} {s : Set X} :
    ContinuousWithinAt f s x ↔ PTendsto (PFun.res f s) (𝓝 x) (𝓝 (f x)) :=
  tendsto_iff_ptendsto _ _ _ _
