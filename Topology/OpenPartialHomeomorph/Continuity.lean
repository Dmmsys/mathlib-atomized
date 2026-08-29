/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
/-!
# Partial homeomorphisms and continuity

## Main theorems

* `OpenPartialHomeomorph.map_nhds_eq`: an open partial homeomorphism preserves the neighbourhood
  filter of any point in its source.
* `OpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left`,
  `OpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_right`: a function is continuous at
  a point iff its pre / post composition with an open partial homeomorphism is so (assuming the
  point is in the source / target).
-/

public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

/--
theorem `eventually_left_inverse` / 定理 `eventually_left_inverse`

English:
theorem eventually_left_inverse
  given: {x} (hx : x in e.source)
  proof: (e.open_source.eventually_mem hx).mono e.left_inv'

中文:
定理 eventually_left_inverse
  条件: {x} (hx : x in e.source)
  证明: (e.open_source.eventually_mem hx).mono e.left_inv'

Depends on / 依赖: e.left_inv, e.open_source.eventually_mem, eventually_mem, left_inv, open_source
-/
theorem eventually_left_inverse {x} (hx : x in e.source) :
    forallᶠ y in 𝓝 x, e.symm (e y) = y :=
  (e.open_source.eventually_mem hx).mono e.left_inv'

/--
theorem `eventually_left_inverse'` / 定理 `eventually_left_inverse'`

English:
theorem eventually_left_inverse'
  given: {x} (hx : x in e.target)
  proof: e.eventually_left_inverse (e.map_target hx)

中文:
定理 eventually_left_inverse'
  条件: {x} (hx : x in e.target)
  证明: e.eventually_left_inverse (e.map_target hx)

Depends on / 依赖: e.eventually_left_inverse, e.map_target, eventually_left_inverse, map_target
-/
theorem eventually_left_inverse' {x} (hx : x in e.target) :
    forallᶠ y in 𝓝 (e.symm x), e.symm (e y) = y :=
  e.eventually_left_inverse (e.map_target hx)

/--
theorem `eventually_right_inverse` / 定理 `eventually_right_inverse`

English:
theorem eventually_right_inverse
  given: {x} (hx : x in e.target)
  proof: (e.open_target.eventually_mem hx).mono e.right_inv'

中文:
定理 eventually_right_inverse
  条件: {x} (hx : x in e.target)
  证明: (e.open_target.eventually_mem hx).mono e.right_inv'

Depends on / 依赖: e.open_target.eventually_mem, e.right_inv, eventually_mem, open_target, right_inv
-/
theorem eventually_right_inverse {x} (hx : x in e.target) :
    forallᶠ y in 𝓝 x, e (e.symm y) = y :=
  (e.open_target.eventually_mem hx).mono e.right_inv'

/--
theorem `eventually_right_inverse'` / 定理 `eventually_right_inverse'`

English:
theorem eventually_right_inverse'
  given: {x} (hx : x in e.source)
  proof: e.eventually_right_inverse (e.map_source hx)

中文:
定理 eventually_right_inverse'
  条件: {x} (hx : x in e.source)
  证明: e.eventually_right_inverse (e.map_source hx)

Depends on / 依赖: e.eventually_right_inverse, e.map_source, eventually_right_inverse, map_source
-/
theorem eventually_right_inverse' {x} (hx : x in e.source) :
    forallᶠ y in 𝓝 (e x), e (e.symm y) = y :=
  e.eventually_right_inverse (e.map_source hx)

/--
theorem `eventually_ne_nhdsWithin` / 定理 `eventually_ne_nhdsWithin`

English:
theorem eventually_ne_nhdsWithin
  given: {x} (hx : x in e.source)
  proof: eventually_nhdsWithin_iff.2
    (e.eventually_left_inverse hx).mono fun x' hx' =>
      mt fun h => by rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']

中文:
定理 eventually_ne_nhdsWithin
  条件: {x} (hx : x in e.source)
  证明: eventually_nhdsWithin_iff.2
    (e.eventually_left_inverse hx).mono fun x' hx' =>
      mt fun h => by rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']

Depends on / 依赖: e.eventually_left_inverse, e.left_inv, eventually_left_inverse, eventually_nhdsWithin_iff, left_inv, mem_singleton_iff
-/
theorem eventually_ne_nhdsWithin {x} (hx : x in e.source) :
    forallᶠ x' in 𝓝[!=] x, e x' != e x :=
eventually_nhdsWithin_iff.2
    (e.eventually_left_inverse hx).mono fun x' hx' =>
      mt fun h => by rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']

/--
theorem `nhdsWithin_source_inter` / 定理 `nhdsWithin_source_inter`

English:
theorem nhdsWithin_source_inter
  given: {x} (hx : x in e.source) (s : Set X)
  statement: 𝓝[e.source inter s] x = 𝓝[s] x
  proof: nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds e.open_source hx)

中文:
定理 nhdsWithin_source_inter
  条件: {x} (hx : x in e.source) (s : 集合 X)
  结论: 𝓝[e.source inter s] x = 𝓝[s] x
  证明: nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds e.open_source hx)

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, e.open_source, mem_nhds, mem_nhdsWithin_of_mem_nhds, nhdsWithin_inter_of_mem, open_source
-/
theorem nhdsWithin_source_inter {x} (hx : x in e.source) (s : Set X) : 𝓝[e.source inter s] x = 𝓝[s] x :=
  nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds e.open_source hx)

/--
theorem `nhdsWithin_target_inter` / 定理 `nhdsWithin_target_inter`

English:
theorem nhdsWithin_target_inter
  given: {x} (hx : x in e.target) (s : Set Y)
  statement: 𝓝[e.target inter s] x = 𝓝[s] x
  proof: e.symm.nhdsWithin_source_inter hx s

中文:
定理 nhdsWithin_target_inter
  条件: {x} (hx : x in e.target) (s : 集合 Y)
  结论: 𝓝[e.target inter s] x = 𝓝[s] x
  证明: e.symm.nhdsWithin_source_inter hx s

Depends on / 依赖: e.symm.nhdsWithin_source_inter, nhdsWithin_source_inter
-/
theorem nhdsWithin_target_inter {x} (hx : x in e.target) (s : Set Y) : 𝓝[e.target inter s] x = 𝓝[s] x :=
  e.symm.nhdsWithin_source_inter hx s

/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  given: {x : X} (h : x in e.source)
  statement: ContinuousAt e x
  proof: (e.continuousOn x h).continuousAt (e.open_source.mem_nhds h)

中文:
定理 continuousAt
  条件: {x : X} (h : x in e.source)
  结论: ContinuousAt e x
  证明: (e.continuousOn x h).continuousAt (e.open_source.mem_nhds h)
-/
protected theorem continuousAt {x : X} (h : x in e.source) : ContinuousAt e x :=
  (e.continuousOn x h).continuousAt (e.open_source.mem_nhds h)

/--
theorem `continuousAt_symm` / 定理 `continuousAt_symm`

English:
theorem continuousAt_symm
  given: {x : Y} (h : x in e.target)
  statement: ContinuousAt e.symm x
  proof: e.symm.continuousAt h

中文:
定理 continuousAt_symm
  条件: {x : Y} (h : x in e.target)
  结论: ContinuousAt e.symm x
  证明: e.symm.continuousAt h

Depends on / 依赖: continuousAt, e.symm.continuousAt
-/
theorem continuousAt_symm {x : Y} (h : x in e.target) : ContinuousAt e.symm x :=
  e.symm.continuousAt h

/--
theorem `tendsto_symm` / 定理 `tendsto_symm`

English:
theorem tendsto_symm
  given: {x} (hx : x in e.source)
  statement: Tendsto e.symm (𝓝 (e x)) (𝓝 x)
  proof: by
  simpa only [ContinuousAt, e.left_inv hx] using e.continuousAt_symm (e.map_source hx)

中文:
定理 tendsto_symm
  条件: {x} (hx : x in e.source)
  结论: 收敛 e.symm (𝓝 (e x)) (𝓝 x)
  证明: by
  simpa only [ContinuousAt, e.left_inv hx] using e.continuousAt_symm (e.map_source hx)

Depends on / 依赖: ContinuousAt, continuousAt_symm, e.continuousAt_symm, e.left_inv, e.map_source, left_inv, map_source
-/
theorem tendsto_symm {x} (hx : x in e.source) : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
  simpa only [ContinuousAt, e.left_inv hx] using e.continuousAt_symm (e.map_source hx)

/--
theorem `map_nhds_eq` / 定理 `map_nhds_eq`

English:
theorem map_nhds_eq
  given: {x} (hx : x in e.source)
  statement: map e (𝓝 x) = 𝓝 (e x)
  proof: le_antisymm (e.continuousAt hx)
    le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)

中文:
定理 map_nhds_eq
  条件: {x} (hx : x in e.source)
  结论: map e (𝓝 x) = 𝓝 (e x)
  证明: le_antisymm (e.continuousAt hx)
    le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)

Depends on / 依赖: continuousAt, e.continuousAt, e.eventually_right_inverse, e.tendsto_symm, eventually_right_inverse, le_antisymm, le_map_of_right_inverse, tendsto_symm
-/
theorem map_nhds_eq {x} (hx : x in e.source) : map e (𝓝 x) = 𝓝 (e x) :=
le_antisymm (e.continuousAt hx)
    le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)

/--
theorem `symm_map_nhds_eq` / 定理 `symm_map_nhds_eq`

English:
theorem symm_map_nhds_eq
  given: {x} (hx : x in e.source)
  statement: map e.symm (𝓝 (e x)) = 𝓝 x
  proof: (e.symm.map_nhds_eq <| e.map_source hx).trans by rw [e.left_inv hx]

中文:
定理 symm_map_nhds_eq
  条件: {x} (hx : x in e.source)
  结论: map e.symm (𝓝 (e x)) = 𝓝 x
  证明: (e.symm.map_nhds_eq <| e.map_source hx).trans by rw [e.left_inv hx]

Depends on / 依赖: e.left_inv, e.map_source, e.symm.map_nhds_eq, left_inv, map_nhds_eq, map_source
-/
theorem symm_map_nhds_eq {x} (hx : x in e.source) : map e.symm (𝓝 (e x)) = 𝓝 x :=
(e.symm.map_nhds_eq <| e.map_source hx).trans by rw [e.left_inv hx]

/--
theorem `image_mem_nhds` / 定理 `image_mem_nhds`

English:
theorem image_mem_nhds
  given: {x} (hx : x in e.source) {s : Set X} (hs : s in 𝓝 x)
  statement: e '' s in 𝓝 (e x)
  proof: e.map_nhds_eq hx ▸ Filter.image_mem_map hs

中文:
定理 image_mem_nhds
  条件: {x} (hx : x in e.source) {s : 集合 X} (hs : s in 𝓝 x)
  结论: e '' s in 𝓝 (e x)
  证明: e.map_nhds_eq hx ▸ Filter.image_mem_map hs

Depends on / 依赖: Filter, Filter.image_mem_map, e.map_nhds_eq, image_mem_map, map_nhds_eq
-/
theorem image_mem_nhds {x} (hx : x in e.source) {s : Set X} (hs : s in 𝓝 x) : e '' s in 𝓝 (e x) :=
  e.map_nhds_eq hx ▸ Filter.image_mem_map hs

/--
theorem `map_nhdsWithin_eq` / 定理 `map_nhdsWithin_eq`

English:
theorem map_nhdsWithin_eq
  given: {x} (hx : x in e.source) (s : Set X)
  proof: calc
    map e (𝓝[s] x) = map e (𝓝[e.source inter s] x) :=
      congr_arg (map e) (e.nhdsWithin_source_inter hx _).symm
    _ = 𝓝[e '' (e.source inter s)] e x :=
      (e.leftInvOn.mono inter_subset_left).map_nhdsWithin_eq (e.left_inv hx)
        (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
        (e.continuousAt hx).continuousWithinAt

中文:
定理 map_nhdsWithin_eq
  条件: {x} (hx : x in e.source) (s : 集合 X)
  证明: calc
    map e (𝓝[s] x) = map e (𝓝[e.source inter s] x) :=
      congr_arg (map e) (e.nhdsWithin_source_inter hx _).symm
    _ = 𝓝[e '' (e.source inter s)] e x :=
      (e.leftInvOn.mono inter_subset_left).map_nhdsWithin_eq (e.left_inv hx)
        (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
        (e.continuousAt hx).continuousWithinAt

Depends on / 依赖: congr_arg, continuousAt, continuousAt_symm, continuousWithinAt, e.continuousAt, e.continuousAt_symm, e.leftInvOn.mono, e.left_inv, e.map_source, e.nhdsWithin_source_inter, e.source, inter_subset_left, leftInvOn, left_inv, map_nhdsWithin_eq, map_source, nhdsWithin_source_inter, source
-/
theorem map_nhdsWithin_eq {x} (hx : x in e.source) (s : Set X) :
    map e (𝓝[s] x) = 𝓝[e '' (e.source inter s)] e x :=
  calc
    map e (𝓝[s] x) = map e (𝓝[e.source inter s] x) :=
      congr_arg (map e) (e.nhdsWithin_source_inter hx _).symm
    _ = 𝓝[e '' (e.source inter s)] e x :=
      (e.leftInvOn.mono inter_subset_left).map_nhdsWithin_eq (e.left_inv hx)
        (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
        (e.continuousAt hx).continuousWithinAt

/--
theorem `map_nhdsWithin_preimage_eq` / 定理 `map_nhdsWithin_preimage_eq`

English:
theorem map_nhdsWithin_preimage_eq
  given: {x} (hx : x in e.source) (s : Set Y)
  proof: by
  rw [e.map_nhdsWithin_eq hx]; rw [e.image_source_inter_eq']; rw [e.target_inter_inv_preimage_preimage]; rw [e.nhdsWithin_target_inter (e.map_source hx)]

中文:
定理 map_nhdsWithin_preimage_eq
  条件: {x} (hx : x in e.source) (s : 集合 Y)
  证明: by
  rw [e.map_nhdsWithin_eq hx]; rw [e.image_source_inter_eq']; rw [e.target_inter_inv_preimage_preimage]; rw [e.nhdsWithin_target_inter (e.map_source hx)]

Depends on / 依赖: e.image_source_inter_eq, e.map_nhdsWithin_eq, e.map_source, e.nhdsWithin_target_inter, e.target_inter_inv_preimage_preimage, image_source_inter_eq, map_nhdsWithin_eq, map_source, nhdsWithin_target_inter, target_inter_inv_preimage_preimage
-/
theorem map_nhdsWithin_preimage_eq {x} (hx : x in e.source) (s : Set Y) :
    map e (𝓝[e ⁻¹' s] x) = 𝓝[s] e x := by
  rw [e.map_nhdsWithin_eq hx]; rw [e.image_source_inter_eq']; rw [e.target_inter_inv_preimage_preimage]; rw [e.nhdsWithin_target_inter (e.map_source hx)]

/--
theorem `eventually_nhds` / 定理 `eventually_nhds`

English:
theorem eventually_nhds
  given: {x : X} (p : Y -> Prop) (hx : x in e.source)
  proof: Iff.trans (by rw [e.map_nhds_eq hx]) eventually_map

中文:
定理 eventually_nhds
  条件: {x : X} (p : Y -> 命题) (hx : x in e.source)
  证明: Iff.trans (by rw [e.map_nhds_eq hx]) eventually_map

Depends on / 依赖: Iff.trans, e.map_nhds_eq, eventually_map, map_nhds_eq
-/
theorem eventually_nhds {x : X} (p : Y -> Prop) (hx : x in e.source) :
    (forallᶠ y in 𝓝 (e x), p y) ↔ forallᶠ x in 𝓝 x, p (e x) :=
  Iff.trans (by rw [e.map_nhds_eq hx]) eventually_map

/--
theorem `eventually_nhds'` / 定理 `eventually_nhds'`

English:
theorem eventually_nhds'
  given: {x : X} (p : X -> Prop) (hx : x in e.source)
  proof: by
  rw [e.eventually_nhds _ hx]
  refine eventually_congr ((e.eventually_left_inverse hx).mono fun y hy => ?_)
  rw [hy]

中文:
定理 eventually_nhds'
  条件: {x : X} (p : X -> 命题) (hx : x in e.source)
  证明: by
  rw [e.eventually_nhds _ hx]
  refine eventually_congr ((e.eventually_left_inverse hx).mono fun y hy => ?_)
  rw [hy]

Depends on / 依赖: e.eventually_left_inverse, e.eventually_nhds, eventually_congr, eventually_left_inverse, eventually_nhds
-/
theorem eventually_nhds' {x : X} (p : X -> Prop) (hx : x in e.source) :
    (forallᶠ y in 𝓝 (e x), p (e.symm y)) ↔ forallᶠ x in 𝓝 x, p x := by
  rw [e.eventually_nhds _ hx]
  refine eventually_congr ((e.eventually_left_inverse hx).mono fun y hy => ?_)
  rw [hy]

/--
theorem `eventually_nhdsWithin` / 定理 `eventually_nhdsWithin`

English:
theorem eventually_nhdsWithin
  statement: {x : X} (p : Y -> Prop) {s : Set X}
  proof: by
  refine Iff.trans ?_ eventually_map
  rw [e.map_nhdsWithin_eq hx]; rw [e.image_source_inter_eq']; rw [e.nhdsWithin_target_inter (e.mapsTo hx)]

中文:
定理 eventually_nhdsWithin
  结论: {x : X} (p : Y -> 命题) {s : 集合 X}
  证明: by
  refine Iff.trans ?_ eventually_map
  rw [e.map_nhdsWithin_eq hx]; rw [e.image_source_inter_eq']; rw [e.nhdsWithin_target_inter (e.mapsTo hx)]

Depends on / 依赖: Iff.trans, e.image_source_inter_eq, e.map_nhdsWithin_eq, e.mapsTo, e.nhdsWithin_target_inter, eventually_map, image_source_inter_eq, map_nhdsWithin_eq, mapsTo, nhdsWithin_target_inter
-/
theorem eventually_nhdsWithin {x : X} (p : Y -> Prop) {s : Set X}
    (hx : x in e.source) : (forallᶠ y in 𝓝[e.symm ⁻¹' s] e x, p y) ↔ forallᶠ x in 𝓝[s] x, p (e x) := by
  refine Iff.trans ?_ eventually_map
  rw [e.map_nhdsWithin_eq hx]; rw [e.image_source_inter_eq']; rw [e.nhdsWithin_target_inter (e.mapsTo hx)]

/--
theorem `eventually_nhdsWithin'` / 定理 `eventually_nhdsWithin'`

English:
theorem eventually_nhdsWithin'
  statement: {x : X} (p : X -> Prop) {s : Set X}
  proof: by
  rw [e.eventually_nhdsWithin _ hx]
refine eventually_congr
    (eventually_nhdsWithin_of_eventually_nhds <| e.eventually_left_inverse hx).mono fun y hy => ?_
  rw [hy]

中文:
定理 eventually_nhdsWithin'
  结论: {x : X} (p : X -> 命题) {s : 集合 X}
  证明: by
  rw [e.eventually_nhdsWithin _ hx]
refine eventually_congr
    (eventually_nhdsWithin_of_eventually_nhds <| e.eventually_left_inverse hx).mono fun y hy => ?_
  rw [hy]

Depends on / 依赖: e.eventually_left_inverse, e.eventually_nhdsWithin, eventually_congr, eventually_left_inverse, eventually_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
-/
theorem eventually_nhdsWithin' {x : X} (p : X -> Prop) {s : Set X}
    (hx : x in e.source) : (forallᶠ y in 𝓝[e.symm ⁻¹' s] e x, p (e.symm y)) ↔ forallᶠ x in 𝓝[s] x, p x := by
  rw [e.eventually_nhdsWithin _ hx]
refine eventually_congr
    (eventually_nhdsWithin_of_eventually_nhds <| e.eventually_left_inverse hx).mono fun y hy => ?_
  rw [hy]

/--
theorem `preimage_eventuallyEq_target_inter_preimage_inter` / 定理 `preimage_eventuallyEq_target_inter_preimage_inter`

English:
theorem preimage_eventuallyEq_target_inter_preimage_inter
  statement: {e : OpenPartialHomeomorph X Y}
  proof: by
  rw [eventuallyEq_set]; rw [e.eventually_nhds _ hxe]
  filter_upwards [e.open_source.mem_nhds hxe,
    mem_nhdsWithin_iff_eventually.mp (hf.preimage_mem_nhdsWithin ht)]
  intro y hy hyu
  simp_rw [mem_inter_iff, mem_preimage, mem_inter_iff, e.mapsTo hy, true_and, iff_self_and,
    e.left_inv hy, iff_true_intro hyu]

中文:
定理 preimage_eventuallyEq_target_inter_preimage_inter
  结论: {e : OpenPartialHomeomorph X Y}
  证明: by
  rw [eventuallyEq_set]; rw [e.eventually_nhds _ hxe]
  filter_upwards [e.open_source.mem_nhds hxe,
    mem_nhdsWithin_iff_eventually.mp (hf.preimage_mem_nhdsWithin ht)]
  intro y hy hyu
  simp_rw [mem_inter_iff, mem_preimage, mem_inter_iff, e.mapsTo hy, true_and, iff_self_and,
    e.left_inv hy, iff_true_intro hyu]

Depends on / 依赖: e.eventually_nhds, e.left_inv, e.mapsTo, e.open_source.mem_nhds, eventuallyEq_set, eventually_nhds, filter_upwards, hf.preimage_mem_nhdsWithin, iff_self_and, iff_true_intro, left_inv, mapsTo, mem_inter_iff, mem_nhds, mem_nhdsWithin_iff_eventually, mem_nhdsWithin_iff_eventually.mp, mem_preimage, open_source, preimage_mem_nhdsWithin, simp_rw
-/
theorem preimage_eventuallyEq_target_inter_preimage_inter {e : OpenPartialHomeomorph X Y}
    {s : Set X} {t : Set Z} {x : X} {f : X -> Z} (hf : ContinuousWithinAt f s x) (hxe : x in e.source)
    (ht : t in 𝓝 (f x)) :
    e.symm ⁻¹' s =ᶠ[𝓝 (e x)] (e.target inter e.symm ⁻¹' (s inter f ⁻¹' t) : Set Y) := by
  rw [eventuallyEq_set]; rw [e.eventually_nhds _ hxe]
  filter_upwards [e.open_source.mem_nhds hxe,
    mem_nhdsWithin_iff_eventually.mp (hf.preimage_mem_nhdsWithin ht)]
  intro y hy hyu
  simp_rw [mem_inter_iff, mem_preimage, mem_inter_iff, e.mapsTo hy, true_and, iff_self_and,
    e.left_inv hy, iff_true_intro hyu]

section Continuity

/--
theorem `continuousWithinAt_iff_continuousWithinAt_comp_right` / 定理 `continuousWithinAt_iff_continuousWithinAt_comp_right`

English:
theorem continuousWithinAt_iff_continuousWithinAt_comp_right
  statement: {f : Y -> Z} {s : Set Y} {x : Y}
  proof: by
  simp_rw [ContinuousWithinAt, ← @tendsto_map'_iff _ _ _ _ e,
    e.map_nhdsWithin_preimage_eq (e.map_target h), (· ∘ ·), e.right_inv h]

中文:
定理 continuousWithinAt_iff_continuousWithinAt_comp_right
  结论: {f : Y -> Z} {s : 集合 Y} {x : Y}
  证明: by
  simp_rw [ContinuousWithinAt, ← @tendsto_map'_iff _ _ _ _ e,
    e.map_nhdsWithin_preimage_eq (e.map_target h), (· ∘ ·), e.right_inv h]

Depends on / 依赖: ContinuousWithinAt, _iff, e.map_nhdsWithin_preimage_eq, e.map_target, e.right_inv, map_nhdsWithin_preimage_eq, map_target, right_inv, simp_rw, tendsto_map
-/
theorem continuousWithinAt_iff_continuousWithinAt_comp_right {f : Y -> Z} {s : Set Y} {x : Y}
    (h : x in e.target) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ∘ e) (e ⁻¹' s) (e.symm x) := by
  simp_rw [ContinuousWithinAt, ← @tendsto_map'_iff _ _ _ _ e,
    e.map_nhdsWithin_preimage_eq (e.map_target h), (· ∘ ·), e.right_inv h]

/--
theorem `continuousAt_iff_continuousAt_comp_right` / 定理 `continuousAt_iff_continuousAt_comp_right`

English:
theorem continuousAt_iff_continuousAt_comp_right
  given: {f : Y -> Z} {x : Y} (h : x in e.target)
  proof: by
  rw [← continuousWithinAt_univ]; rw [e.continuousWithinAt_iff_continuousWithinAt_comp_right h]; rw [preimage_univ]; rw [continuousWithinAt_univ]

中文:
定理 continuousAt_iff_continuousAt_comp_right
  条件: {f : Y -> Z} {x : Y} (h : x in e.target)
  证明: by
  rw [← continuousWithinAt_univ]; rw [e.continuousWithinAt_iff_continuousWithinAt_comp_right h]; rw [preimage_univ]; rw [continuousWithinAt_univ]

Depends on / 依赖: continuousWithinAt_iff_continuousWithinAt_comp_right, continuousWithinAt_univ, e.continuousWithinAt_iff_continuousWithinAt_comp_right, preimage_univ
-/
theorem continuousAt_iff_continuousAt_comp_right {f : Y -> Z} {x : Y} (h : x in e.target) :
    ContinuousAt f x ↔ ContinuousAt (f ∘ e) (e.symm x) := by
  rw [← continuousWithinAt_univ]; rw [e.continuousWithinAt_iff_continuousWithinAt_comp_right h]; rw [preimage_univ]; rw [continuousWithinAt_univ]

/--
theorem `continuousOn_iff_continuousOn_comp_right` / 定理 `continuousOn_iff_continuousOn_comp_right`

English:
theorem continuousOn_iff_continuousOn_comp_right
  given: {f : Y -> Z} {s : Set Y} (h : s subseteq e.target)
  proof: by
  simp only [← e.symm_image_eq_source_inter_preimage h, ContinuousOn, forall_mem_image]
  refine forall₂_congr fun x hx => ?_
  rw [e.continuousWithinAt_iff_continuousWithinAt_comp_right (h hx)]; rw [e.symm_image_eq_source_inter_preimage h]; rw [inter_comm]; rw [continuousWithinAt_inter]
  exact IsOpen.mem_nhds e.open_source (e.map_target (h hx))

中文:
定理 continuousOn_iff_continuousOn_comp_right
  条件: {f : Y -> Z} {s : 集合 Y} (h : s subseteq e.target)
  证明: by
  simp only [← e.symm_image_eq_source_inter_preimage h, ContinuousOn, forall_mem_image]
  refine forall₂_congr fun x hx => ?_
  rw [e.continuousWithinAt_iff_continuousWithinAt_comp_right (h hx)]; rw [e.symm_image_eq_source_inter_preimage h]; rw [inter_comm]; rw [continuousWithinAt_inter]
  exact IsOpen.mem_nhds e.open_source (e.map_target (h hx))

Depends on / 依赖: ContinuousOn, IsOpen, IsOpen.mem_nhds, continuousWithinAt_iff_continuousWithinAt_comp_right, continuousWithinAt_inter, e.continuousWithinAt_iff_continuousWithinAt_comp_right, e.map_target, e.open_source, e.symm_image_eq_source_inter_preimage, forall_mem_image, inter_comm, map_target, mem_nhds, open_source, symm_image_eq_source_inter_preimage
-/
theorem continuousOn_iff_continuousOn_comp_right {f : Y -> Z} {s : Set Y} (h : s subseteq e.target) :
    ContinuousOn f s ↔ ContinuousOn (f ∘ e) (e.source inter e ⁻¹' s) := by
  simp only [← e.symm_image_eq_source_inter_preimage h, ContinuousOn, forall_mem_image]
  refine forall₂_congr fun x hx => ?_
  rw [e.continuousWithinAt_iff_continuousWithinAt_comp_right (h hx)]; rw [e.symm_image_eq_source_inter_preimage h]; rw [inter_comm]; rw [continuousWithinAt_inter]
  exact IsOpen.mem_nhds e.open_source (e.map_target (h hx))

/--
theorem `continuousWithinAt_iff_continuousWithinAt_comp_left` / 定理 `continuousWithinAt_iff_continuousWithinAt_comp_left`

English:
theorem continuousWithinAt_iff_continuousWithinAt_comp_left
  statement: {f : Z -> X} {s : Set Z} {x : Z}
  proof: by
  refine ⟨(e.continuousAt hx).comp_continuousWithinAt, fun fe_cont => ?_⟩
  rw [← continuousWithinAt_inter' h] at fe_cont ⊢
  have : ContinuousWithinAt (e.symm ∘ e ∘ f) (s inter f ⁻¹' e.source) x :=
    haveI : ContinuousWithinAt e.symm univ (e (f x)) :=
      (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
    ContinuousWithinAt.comp this fe_cont (subset_univ _)
  exact this.congr (fun y hy => by simp [e.left_inv hy.2]) (by simp [e.left_inv hx])

中文:
定理 continuousWithinAt_iff_continuousWithinAt_comp_left
  结论: {f : Z -> X} {s : 集合 Z} {x : Z}
  证明: by
  refine ⟨(e.continuousAt hx).comp_continuousWithinAt, fun fe_cont => ?_⟩
  rw [← continuousWithinAt_inter' h] at fe_cont ⊢
  have : ContinuousWithinAt (e.symm ∘ e ∘ f) (s inter f ⁻¹' e.source) x :=
    haveI : ContinuousWithinAt e.symm univ (e (f x)) :=
      (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
    ContinuousWithinAt.comp this fe_cont (subset_univ _)
  exact this.congr (fun y hy => by simp [e.left_inv hy.2]) (by simp [e.left_inv hx])

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.comp, comp_continuousWithinAt, continuousAt, continuousAt_symm, continuousWithinAt, continuousWithinAt_inter, e.continuousAt, e.continuousAt_symm, e.left_inv, e.map_source, e.source, e.symm, fe_cont, left_inv, map_source, source, subset_univ, this.congr
-/
theorem continuousWithinAt_iff_continuousWithinAt_comp_left {f : Z -> X} {s : Set Z} {x : Z}
    (hx : f x in e.source) (h : f ⁻¹' e.source in 𝓝[s] x) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (e ∘ f) s x := by
  refine ⟨(e.continuousAt hx).comp_continuousWithinAt, fun fe_cont => ?_⟩
  rw [← continuousWithinAt_inter' h] at fe_cont ⊢
  have : ContinuousWithinAt (e.symm ∘ e ∘ f) (s inter f ⁻¹' e.source) x :=
    haveI : ContinuousWithinAt e.symm univ (e (f x)) :=
      (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
    ContinuousWithinAt.comp this fe_cont (subset_univ _)
  exact this.congr (fun y hy => by simp [e.left_inv hy.2]) (by simp [e.left_inv hx])

/--
theorem `continuousAt_iff_continuousAt_comp_left` / 定理 `continuousAt_iff_continuousAt_comp_left`

English:
theorem continuousAt_iff_continuousAt_comp_left
  given: {f : Z -> X} {x : Z} (h : f ⁻¹' e.source in 𝓝 x)
  proof: by
  have hx : f x in e.source := (mem_of_mem_nhds h :)
  have h' : f ⁻¹' e.source in 𝓝[univ] x := by rwa [nhdsWithin_univ]
  rw [← continuousWithinAt_univ]; rw [← continuousWithinAt_univ]; rw [e.continuousWithinAt_iff_continuousWithinAt_comp_left hx h']

中文:
定理 continuousAt_iff_continuousAt_comp_left
  条件: {f : Z -> X} {x : Z} (h : f ⁻¹' e.source in 𝓝 x)
  证明: by
  have hx : f x in e.source := (mem_of_mem_nhds h :)
  have h' : f ⁻¹' e.source in 𝓝[univ] x := by rwa [nhdsWithin_univ]
  rw [← continuousWithinAt_univ]; rw [← continuousWithinAt_univ]; rw [e.continuousWithinAt_iff_continuousWithinAt_comp_left hx h']

Depends on / 依赖: continuousWithinAt_iff_continuousWithinAt_comp_left, continuousWithinAt_univ, e.continuousWithinAt_iff_continuousWithinAt_comp_left, e.source, mem_of_mem_nhds, nhdsWithin_univ, source
-/
theorem continuousAt_iff_continuousAt_comp_left {f : Z -> X} {x : Z} (h : f ⁻¹' e.source in 𝓝 x) :
    ContinuousAt f x ↔ ContinuousAt (e ∘ f) x := by
  have hx : f x in e.source := (mem_of_mem_nhds h :)
  have h' : f ⁻¹' e.source in 𝓝[univ] x := by rwa [nhdsWithin_univ]
  rw [← continuousWithinAt_univ]; rw [← continuousWithinAt_univ]; rw [e.continuousWithinAt_iff_continuousWithinAt_comp_left hx h']

/--
theorem `continuousOn_iff_continuousOn_comp_left` / 定理 `continuousOn_iff_continuousOn_comp_left`

English:
theorem continuousOn_iff_continuousOn_comp_left
  given: {f : Z -> X} {s : Set Z} (h : s subseteq f ⁻¹' e.source)
  proof: forall₂_congr fun _x hx =>
    e.continuousWithinAt_iff_continuousWithinAt_comp_left (h hx)
      (mem_of_superset self_mem_nhdsWithin h)

中文:
定理 continuousOn_iff_continuousOn_comp_left
  条件: {f : Z -> X} {s : 集合 Z} (h : s subseteq f ⁻¹' e.source)
  证明: forall₂_congr fun _x hx =>
    e.continuousWithinAt_iff_continuousWithinAt_comp_left (h hx)
      (mem_of_superset self_mem_nhdsWithin h)

Depends on / 依赖: continuousWithinAt_iff_continuousWithinAt_comp_left, e.continuousWithinAt_iff_continuousWithinAt_comp_left, mem_of_superset, self_mem_nhdsWithin
-/
theorem continuousOn_iff_continuousOn_comp_left {f : Z -> X} {s : Set Z} (h : s subseteq f ⁻¹' e.source) :
    ContinuousOn f s ↔ ContinuousOn (e ∘ f) s :=
  forall₂_congr fun _x hx =>
    e.continuousWithinAt_iff_continuousWithinAt_comp_left (h hx)
      (mem_of_superset self_mem_nhdsWithin h)

/--
theorem `continuous_iff_continuous_comp_left` / 定理 `continuous_iff_continuous_comp_left`

English:
theorem continuous_iff_continuous_comp_left
  given: {f : Z -> X} (h : f ⁻¹' e.source = univ)
  proof: by
  simp only [← continuousOn_univ]
  exact e.continuousOn_iff_continuousOn_comp_left (Eq.symm h).subset

中文:
定理 continuous_iff_continuous_comp_left
  条件: {f : Z -> X} (h : f ⁻¹' e.source = univ)
  证明: by
  simp only [← continuousOn_univ]
  exact e.continuousOn_iff_continuousOn_comp_left (Eq.symm h).subset

Depends on / 依赖: Eq.symm, continuousOn_iff_continuousOn_comp_left, continuousOn_univ, e.continuousOn_iff_continuousOn_comp_left, subset
-/
theorem continuous_iff_continuous_comp_left {f : Z -> X} (h : f ⁻¹' e.source = univ) :
    Continuous f ↔ Continuous (e ∘ f) := by
  simp only [← continuousOn_univ]
  exact e.continuousOn_iff_continuousOn_comp_left (Eq.symm h).subset

end Continuity

end OpenPartialHomeomorph
