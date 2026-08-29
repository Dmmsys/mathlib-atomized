/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# Local properties invariant under a groupoid

We study properties of a triple `(g, s, x)` where `g` is a function between two spaces `H` and `H'`,
`s` is a subset of `H` and `x` is a point of `H`. Our goal is to register how such a property
should behave to make sense in charted spaces modelled on `H` and `H'`.

The main examples we have in mind are the properties "`g` is differentiable at `x` within `s`", or
"`g` is smooth at `x` within `s`". We want to develop general results that, when applied in these
specific situations, say that the notion of smooth function in a manifold behaves well under
restriction, intersection, is local, and so on.

## Main definitions

* `LocalInvariantProp G G' P` says that a property `P` of a triple `(g, s, x)` is local, and
  invariant under composition by elements of the groupoids `G` and `G'` of `H` and `H'`
  respectively.
* `ChartedSpace.LiftPropWithinAt` (resp. `LiftPropAt`, `LiftPropOn` and `LiftProp`):
  given a property `P` of `(g, s, x)` where `g : H → H'`, define the corresponding property
  for functions `M → M'` where `M` and `M'` are charted spaces modelled respectively on `H` and
  `H'`. We define these properties within a set at a point, or at a point, or on a set, or in the
  whole space. This lifting process (obtained by restricting to suitable chart domains) can always
  be done, but it only behaves well under locality and invariance assumptions.

Given `hG : LocalInvariantProp G G' P`, we deduce many properties of the lifted property on the
charted spaces. For instance, `hG.liftPropWithinAt_inter` says that `P g s x` is equivalent to
`P g (s ∩ t) x` whenever `t` is a neighborhood of `x`.

## Implementation notes

We do not use dot notation for properties of the lifted property. For instance, we have
`hG.liftPropWithinAt_congr` saying that if `LiftPropWithinAt P g s x` holds, and `g` and `g'`
coincide on `s`, then `LiftPropWithinAt P g' s x` holds. We can't call it
`LiftPropWithinAt.congr` as it is in the namespace associated to `LocalInvariantProp`, not
in the one for `LiftPropWithinAt`.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold Topology

variable {H M H' M' X : Type*}
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace H'] [TopologicalSpace M'] [ChartedSpace H' M']
variable [TopologicalSpace X]

namespace StructureGroupoid

variable (G : StructureGroupoid H) (G' : StructureGroupoid H')

/--
Definition of `LocalInvariantProp` / `LocalInvariantProp` 的定义

English:
structure LocalInvariantProp
  parameters: (P : (H -> H') -> Set H -> H -> Prop)
  axioms and operations (4):
    - is_local : forall {s x u} {f : H -> H'}, IsOpen u -> x in u -> (P f s x ↔ P f (s inter u) x)
    - right_invariance' : forall {s x f} {e : OpenPartialHomeomorph H H}, e in G -> x in e.source -> P f s x -> P (f ∘ e.symm) (e.symm ⁻¹' s) (e x)
    - congr_of_forall : forall {s x} {f g : H -> H'}, (forall y in s, f y = g y) -> f x = g x -> P f s x -> P g s x
    - left_invariance' : forall {s x f} {e' : OpenPartialHomeomorph H' H'}, e' in G' -> s subseteq f ⁻¹' e'.source -> f x in e'.source -> P f s x -> P (e' ∘ f) s x

中文:
结构 LocalInvariantProp
  参数: (P : (H -> H') -> Set H -> H -> 命题)
  公理与运算 (4 个):
    - is_local : 对任意 {s x u} {f : H -> H'}, IsOpen u -> x in u -> (P f s x ↔ P f (s inter u) x)
    - right_invariance' : 对任意 {s x f} {e : OpenPartialHomeomorph H H}, e in G -> x in e.source -> P f s x -> P (f ∘ e.symm) (e.symm ⁻¹' s) (e x)
    - congr_of_forall : 对任意 {s x} {f g : H -> H'}, (对任意 y in s, f y = g y) -> f x = g x -> P f s x -> P g s x
    - left_invariance' : 对任意 {s x f} {e' : OpenPartialHomeomorph H' H'}, e' in G' -> s subseteq f ⁻¹' e'.source -> f x in e'.source -> P f s x -> P (e' ∘ f) s x
-/
structure LocalInvariantProp (P : (H -> H') -> Set H -> H -> Prop) : Prop where
  is_local : forall {s x u} {f : H -> H'}, IsOpen u -> x in u -> (P f s x ↔ P f (s inter u) x)
  right_invariance' : forall {s x f} {e : OpenPartialHomeomorph H H},
    e in G -> x in e.source -> P f s x -> P (f ∘ e.symm) (e.symm ⁻¹' s) (e x)
  congr_of_forall : forall {s x} {f g : H -> H'}, (forall y in s, f y = g y) -> f x = g x -> P f s x -> P g s x
  left_invariance' : forall {s x f} {e' : OpenPartialHomeomorph H' H'},
    e' in G' -> s subseteq f ⁻¹' e'.source -> f x in e'.source -> P f s x -> P (e' ∘ f) s x

variable {G G'} {P : (H -> H') -> Set H -> H -> Prop}
variable (hG : G.LocalInvariantProp G' P)
include hG

namespace LocalInvariantProp

/--
theorem `congr_set` / 定理 `congr_set`

English:
theorem congr_set
  given: {s t : Set H} {x : H} {f : H -> H'} (hu : s =ᶠ[𝓝 x] t)
  statement: P f s x ↔ P f t x
  proof: by
  obtain ⟨o, host, ho, hxo⟩ := mem_nhds_iff.mp hu.mem_iff
  simp_rw [subset_def, mem_ofPred, ← and_congr_left_iff, ← mem_inter_iff, ← Set.ext_iff] at host
  rw [hG.is_local ho hxo]; rw [host]; rw [← hG.is_local ho hxo]

中文:
定理 congr_set
  条件: {s t : Set H} {x : H} {f : H -> H'} (hu : s =ᶠ[𝓝 x] t)
  结论: P f s x ↔ P f t x
  证明: by
  obtain ⟨o, host, ho, hxo⟩ := mem_nhds_iff.mp hu.mem_iff
  simp_rw [subset_def, mem_ofPred, ← and_congr_left_iff, ← mem_inter_iff, ← Set.ext_iff] at host
  rw [hG.is_local ho hxo]; rw [host]; rw [← hG.is_local ho hxo]

Depends on / 依赖: Set.ext_iff, and_congr_left_iff, ext_iff, hG.is_local, hu.mem_iff, is_local, mem_iff, mem_inter_iff, mem_nhds_iff, mem_nhds_iff.mp, mem_ofPred, simp_rw, subset_def
-/
theorem congr_set {s t : Set H} {x : H} {f : H -> H'} (hu : s =ᶠ[𝓝 x] t) : P f s x ↔ P f t x := by
  obtain ⟨o, host, ho, hxo⟩ := mem_nhds_iff.mp hu.mem_iff
  simp_rw [subset_def, mem_ofPred, ← and_congr_left_iff, ← mem_inter_iff, ← Set.ext_iff] at host
  rw [hG.is_local ho hxo]; rw [host]; rw [← hG.is_local ho hxo]

/--
theorem `is_local_nhds` / 定理 `is_local_nhds`

English:
theorem is_local_nhds
  given: {s u : Set H} {x : H} {f : H -> H'} (hu : u in 𝓝[s] x)
  proof: hG.congr_set mem_nhdsWithin_iff_eventuallyEq.mp hu

中文:
定理 is_local_nhds
  条件: {s u : Set H} {x : H} {f : H -> H'} (hu : u in 𝓝[s] x)
  证明: hG.congr_set mem_nhdsWithin_iff_eventuallyEq.mp hu

Depends on / 依赖: congr_set, hG.congr_set, mem_nhdsWithin_iff_eventuallyEq, mem_nhdsWithin_iff_eventuallyEq.mp
-/
theorem is_local_nhds {s u : Set H} {x : H} {f : H -> H'} (hu : u in 𝓝[s] x) :
    P f s x ↔ P f (s inter u) x :=
hG.congr_set mem_nhdsWithin_iff_eventuallyEq.mp hu

/--
theorem `congr_iff_nhdsWithin` / 定理 `congr_iff_nhdsWithin`

English:
theorem congr_iff_nhdsWithin
  statement: {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g)
  proof: by
  simp_rw [hG.is_local_nhds h1]
  exact ⟨hG.congr_of_forall (fun y hy => hy.2) h2, hG.congr_of_forall (fun y hy => hy.2.symm) h2.symm⟩

中文:
定理 congr_iff_nhdsWithin
  结论: {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g)
  证明: by
  simp_rw [hG.is_local_nhds h1]
  exact ⟨hG.congr_of_forall (fun y hy => hy.2) h2, hG.congr_of_forall (fun y hy => hy.2.symm) h2.symm⟩

Depends on / 依赖: congr_of_forall, h2.symm, hG.congr_of_forall, hG.is_local_nhds, is_local_nhds, simp_rw
-/
theorem congr_iff_nhdsWithin {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g)
    (h2 : f x = g x) : P f s x ↔ P g s x := by
  simp_rw [hG.is_local_nhds h1]
  exact ⟨hG.congr_of_forall (fun y hy => hy.2) h2, hG.congr_of_forall (fun y hy => hy.2.symm) h2.symm⟩

/--
theorem `congr_nhdsWithin` / 定理 `congr_nhdsWithin`

English:
theorem congr_nhdsWithin
  statement: {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
  proof: (hG.congr_iff_nhdsWithin h1 h2).mp hP

中文:
定理 congr_nhdsWithin
  结论: {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
  证明: (hG.congr_iff_nhdsWithin h1 h2).mp hP

Depends on / 依赖: congr_iff_nhdsWithin, hG.congr_iff_nhdsWithin
-/
theorem congr_nhdsWithin {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
    (hP : P f s x) : P g s x :=
  (hG.congr_iff_nhdsWithin h1 h2).mp hP

/--
theorem `congr_nhdsWithin'` / 定理 `congr_nhdsWithin'`

English:
theorem congr_nhdsWithin'
  statement: {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
  proof: (hG.congr_iff_nhdsWithin h1 h2).mpr hP

中文:
定理 congr_nhdsWithin'
  结论: {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
  证明: (hG.congr_iff_nhdsWithin h1 h2).mpr hP

Depends on / 依赖: congr_iff_nhdsWithin, hG.congr_iff_nhdsWithin
-/
theorem congr_nhdsWithin' {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
    (hP : P g s x) : P f s x :=
  (hG.congr_iff_nhdsWithin h1 h2).mpr hP

/--
theorem `congr_iff` / 定理 `congr_iff`

English:
theorem congr_iff
  given: {s : Set H} {x : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g)
  statement: P f s x ↔ P g s x
  proof: hG.congr_iff_nhdsWithin (mem_nhdsWithin_of_mem_nhds h) (mem_of_mem_nhds h :)

中文:
定理 congr_iff
  条件: {s : Set H} {x : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g)
  结论: P f s x ↔ P g s x
  证明: hG.congr_iff_nhdsWithin (mem_nhdsWithin_of_mem_nhds h) (mem_of_mem_nhds h :)

Depends on / 依赖: congr_iff_nhdsWithin, hG.congr_iff_nhdsWithin, mem_nhdsWithin_of_mem_nhds, mem_of_mem_nhds
-/
theorem congr_iff {s : Set H} {x : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) : P f s x ↔ P g s x :=
  hG.congr_iff_nhdsWithin (mem_nhdsWithin_of_mem_nhds h) (mem_of_mem_nhds h :)

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  given: {s : Set H} {x : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) (hP : P f s x)
  statement: P g s x
  proof: (hG.congr_iff h).mp hP

中文:
定理 congr
  条件: {s : Set H} {x : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) (hP : P f s x)
  结论: P g s x
  证明: (hG.congr_iff h).mp hP

Depends on / 依赖: congr_iff, hG.congr_iff
-/
theorem congr {s : Set H} {x : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) (hP : P f s x) : P g s x :=
  (hG.congr_iff h).mp hP

/--
theorem `congr'` / 定理 `congr'`

English:
theorem congr'
  given: {s : Set H} {x : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) (hP : P g s x)
  statement: P f s x
  proof: hG.congr h.symm hP

中文:
定理 congr'
  条件: {s : Set H} {x : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) (hP : P g s x)
  结论: P f s x
  证明: hG.congr h.symm hP

Depends on / 依赖: h.symm, hG.congr
-/
theorem congr' {s : Set H} {x : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) (hP : P g s x) : P f s x :=
  hG.congr h.symm hP

/--
theorem `congr_set_fun` / 定理 `congr_set_fun`

English:
theorem congr_set_fun
  given: {s t : Set H} {x : H} {f g : H -> H'} (hu : s =ᶠ[𝓝 x] t) (h : f =ᶠ[𝓝 x] g)
  proof: by
  rw [hG.congr_iff h]; rw [hG.congr_set hu]

中文:
定理 congr_set_fun
  条件: {s t : Set H} {x : H} {f g : H -> H'} (hu : s =ᶠ[𝓝 x] t) (h : f =ᶠ[𝓝 x] g)
  证明: by
  rw [hG.congr_iff h]; rw [hG.congr_set hu]

Depends on / 依赖: congr_iff, congr_set, hG.congr_iff, hG.congr_set
-/
theorem congr_set_fun {s t : Set H} {x : H} {f g : H -> H'} (hu : s =ᶠ[𝓝 x] t) (h : f =ᶠ[𝓝 x] g) :
    P f s x ↔ P g t x := by
  rw [hG.congr_iff h]; rw [hG.congr_set hu]

/--
theorem `left_invariance` / 定理 `left_invariance`

English:
theorem left_invariance
  statement: {s : Set H} {x : H} {f : H -> H'} {e' : OpenPartialHomeomorph H' H'}
  proof: by
  have h2f := hfs.preimage_mem_nhdsWithin (e'.open_source.mem_nhds hxe')
  have h3f :=
((e'.continuousAt hxe').comp_continuousWithinAt hfs).preimage_mem_nhdsWithin
e'.symm.open_source.mem_nhds e'.mapsTo hxe'
  constructor
  · intro h
    rw [hG.is_local_nhds h3f] at h
    have h2 := hG.left_invar

中文:
定理 left_invariance
  结论: {s : Set H} {x : H} {f : H -> H'} {e' : OpenPartialHomeomorph H' H'}
  证明: by
  have h2f := hfs.preimage_mem_nhdsWithin (e'.open_source.mem_nhds hxe')
  have h3f :=
((e'.continuousAt hxe').comp_continuousWithinAt hfs).preimage_mem_nhdsWithin
e'.symm.open_source.mem_nhds e'.mapsTo hxe'
  constructor
  · intro h
    rw [hG.is_local_nhds h3f] at h
    have h2 := hG.left_invar

Depends on / 依赖: comp_continuousWithinAt, congr_nhdsWithin, continuousAt, eventually_of_mem, hG.congr_nhdsWithin, hG.is_loca, hG.is_local_nhds, hG.left_invariance, hfs.preimage_mem_nhdsWithin, inter_subset_right, is_loca, is_local_nhds, left_inv, left_invariance, mapsTo, mem_nhds, open_source, open_source.mem_nhds, preimage_mem_nhdsWithin, simp_rw
-/
theorem left_invariance {s : Set H} {x : H} {f : H -> H'} {e' : OpenPartialHomeomorph H' H'}
    (he' : e' in G') (hfs : ContinuousWithinAt f s x) (hxe' : f x in e'.source) :
    P (e' ∘ f) s x ↔ P f s x := by
  have h2f := hfs.preimage_mem_nhdsWithin (e'.open_source.mem_nhds hxe')
  have h3f :=
((e'.continuousAt hxe').comp_continuousWithinAt hfs).preimage_mem_nhdsWithin
e'.symm.open_source.mem_nhds e'.mapsTo hxe'
  constructor
  · intro h
    rw [hG.is_local_nhds h3f] at h
    have h2 := hG.left_invariance' (G'.symm he') inter_subset_right (e'.mapsTo hxe') h
    rw [← hG.is_local_nhds h3f] at h2
    refine hG.congr_nhdsWithin ?_ (e'.left_inv hxe') h2
    exact eventually_of_mem h2f fun x' => e'.left_inv
  · simp_rw [hG.is_local_nhds h2f]
    exact hG.left_invariance' he' inter_subset_right hxe'

/--
theorem `right_invariance` / 定理 `right_invariance`

English:
theorem right_invariance
  statement: {s : Set H} {x : H} {f : H -> H'} {e : OpenPartialHomeomorph H H}
  proof: by
  refine ⟨fun h => ?_, hG.right_invariance' he hxe⟩
  have := hG.right_invariance' (G.symm he) (e.mapsTo hxe) h
  rw [e.symm_symm]; rw [e.left_inv hxe] at this
  refine hG.congr ?_ ((hG.congr_set ?_).mp this)
  · refine eventually_of_mem (e.open_source.mem_nhds hxe) fun x' hx' => ?_
    simp_rw [

中文:
定理 right_invariance
  结论: {s : Set H} {x : H} {f : H -> H'} {e : OpenPartialHomeomorph H H}
  证明: by
  refine ⟨fun h => ?_, hG.right_invariance' he hxe⟩
  have := hG.right_invariance' (G.symm he) (e.mapsTo hxe) h
  rw [e.symm_symm]; rw [e.left_inv hxe] at this
  refine hG.congr ?_ ((hG.congr_set ?_).mp this)
  · refine eventually_of_mem (e.open_source.mem_nhds hxe) fun x' hx' => ?_
    simp_rw [

Depends on / 依赖: Function, Function.comp_apply, G.symm, comp_apply, congr_set, e.left_inv, e.mapsTo, e.open_source.mem_nhds, e.symm_symm, eventuallyEq_set, eventually_of_mem, hG.congr, hG.congr_set, hG.right_invariance, left_inv, mapsTo, mem_nhds, mem_preimage, open_source, right_invariance
-/
theorem right_invariance {s : Set H} {x : H} {f : H -> H'} {e : OpenPartialHomeomorph H H}
    (he : e in G) (hxe : x in e.source) : P (f ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P f s x := by
  refine ⟨fun h => ?_, hG.right_invariance' he hxe⟩
  have := hG.right_invariance' (G.symm he) (e.mapsTo hxe) h
  rw [e.symm_symm]; rw [e.left_inv hxe] at this
  refine hG.congr ?_ ((hG.congr_set ?_).mp this)
  · refine eventually_of_mem (e.open_source.mem_nhds hxe) fun x' hx' => ?_
    simp_rw [Function.comp_apply, e.left_inv hx']
  · rw [eventuallyEq_set]
    refine eventually_of_mem (e.open_source.mem_nhds hxe) fun x' hx' => ?_
    simp_rw [mem_preimage, e.left_inv hx']

end LocalInvariantProp

end StructureGroupoid

namespace ChartedSpace

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property in a charted space, by requiring that it holds at the preferred chart at
this point. (When the property is local and invariant, it will in fact hold using any chart, see
`liftPropWithinAt_indep_chart`). We require continuity in the lifted property, as otherwise one
single chart might fail to capture the behavior of the function.
-/
@[mk_iff liftPropWithinAt_iff']
/--
Definition of `LiftPropWithinAt` / `LiftPropWithinAt` 的定义

English:
structure LiftPropWithinAt
  parameters: (P : (H -> H') -> Set H -> H -> Prop) (f : M -> M') (s : Set M) (x : M)
  axioms and operations (2):
    - continuousWithinAt : ContinuousWithinAt f s x
    - prop : P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x)

中文:
结构 LiftPropWithinAt
  参数: (P : (H -> H') -> Set H -> H -> 命题) (f : M -> M') (s : Set M) (x : M)
  公理与运算 (2 个):
    - continuousWithinAt : ContinuousWithinAt f s x
    - prop : P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x)
-/
structure LiftPropWithinAt (P : (H -> H') -> Set H -> H -> Prop) (f : M -> M') (s : Set M) (x : M) :
    Prop where
  continuousWithinAt : ContinuousWithinAt f s x
  prop : P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x)

/--
Definition of `LiftPropOn` / `LiftPropOn` 的定义

English:
definition LiftPropOn
  signature: (P : (H -> H') -> Set H -> H -> Prop) (f : M -> M') (s : Set M)
  body: forall x in s, LiftPropWithinAt P f s x

中文:
定义 LiftPropOn
  签名: (P : (H -> H') -> Set H -> H -> 命题) (f : M -> M') (s : Set M)
  定义体: forall x in s, LiftPropWithinAt P f s x

Depends on / 依赖: LiftPropWithinAt
-/
def LiftPropOn (P : (H -> H') -> Set H -> H -> Prop) (f : M -> M') (s : Set M) :=
  forall x in s, LiftPropWithinAt P f s x

/--
Definition of `LiftPropAt` / `LiftPropAt` 的定义

English:
definition LiftPropAt
  signature: (P : (H -> H') -> Set H -> H -> Prop) (f : M -> M') (x : M)
  body: LiftPropWithinAt P f univ x

中文:
定义 LiftPropAt
  签名: (P : (H -> H') -> Set H -> H -> 命题) (f : M -> M') (x : M)
  定义体: LiftPropWithinAt P f univ x

Depends on / 依赖: LiftPropWithinAt
-/
def LiftPropAt (P : (H -> H') -> Set H -> H -> Prop) (f : M -> M') (x : M) :=
  LiftPropWithinAt P f univ x

/--
theorem `liftPropAt_iff` / 定理 `liftPropAt_iff`

English:
theorem liftPropAt_iff
  given: {P : (H -> H') -> Set H -> H -> Prop} {f : M -> M'} {x : M}
  proof: by
  rw [LiftPropAt]; rw [liftPropWithinAt_iff']; rw [continuousWithinAt_univ]; rw [preimage_univ]

中文:
定理 liftPropAt_iff
  条件: {P : (H -> H') -> Set H -> H -> 命题} {f : M -> M'} {x : M}
  证明: by
  rw [LiftPropAt]; rw [liftPropWithinAt_iff']; rw [continuousWithinAt_univ]; rw [preimage_univ]

Depends on / 依赖: LiftPropAt, continuousWithinAt_univ, liftPropWithinAt_iff, preimage_univ
-/
theorem liftPropAt_iff {P : (H -> H') -> Set H -> H -> Prop} {f : M -> M'} {x : M} :
    LiftPropAt P f x ↔
      ContinuousAt f x ∧ P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) univ (chartAt H x x) := by
  rw [LiftPropAt]; rw [liftPropWithinAt_iff']; rw [continuousWithinAt_univ]; rw [preimage_univ]

/--
Definition of `LiftProp` / `LiftProp` 的定义

English:
definition LiftProp
  signature: (P : (H -> H') -> Set H -> H -> Prop) (f : M -> M')
  body: forall x, LiftPropAt P f x

中文:
定义 LiftProp
  签名: (P : (H -> H') -> Set H -> H -> 命题) (f : M -> M')
  定义体: forall x, LiftPropAt P f x

Depends on / 依赖: LiftPropAt
-/
def LiftProp (P : (H -> H') -> Set H -> H -> Prop) (f : M -> M') :=
  forall x, LiftPropAt P f x

/--
theorem `liftProp_iff` / 定理 `liftProp_iff`

English:
theorem liftProp_iff
  given: {P : (H -> H') -> Set H -> H -> Prop} {f : M -> M'}
  proof: by
  simp_rw [LiftProp, liftPropAt_iff, forall_and, continuous_iff_continuousAt]

@[simp]

中文:
定理 liftProp_iff
  条件: {P : (H -> H') -> Set H -> H -> 命题} {f : M -> M'}
  证明: by
  simp_rw [LiftProp, liftPropAt_iff, forall_and, continuous_iff_continuousAt]

@[simp]

Depends on / 依赖: LiftProp, continuous_iff_continuousAt, forall_and, liftPropAt_iff, simp_rw
-/
theorem liftProp_iff {P : (H -> H') -> Set H -> H -> Prop} {f : M -> M'} :
    LiftProp P f ↔
      Continuous f ∧ forall x, P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) univ (chartAt H x x) := by
  simp_rw [LiftProp, liftPropAt_iff, forall_and, continuous_iff_continuousAt]

@[simp]
/--
lemma `liftPropWithinAt_subtypeVal_comp_iff` / 引理 `liftPropWithinAt_subtypeVal_comp_iff`

English:
lemma liftPropWithinAt_subtypeVal_comp_iff
  statement: {P : (H -> H') -> Set H -> H -> Prop}
  proof: by
  simp only [ChartedSpace.liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · exact Topology.IsEmbedding.subtypeVal.isInducing.continuousWithinAt_iff.symm
  · rfl

中文:
引理 liftPropWithinAt_subtypeVal_comp_iff
  结论: {P : (H -> H') -> Set H -> H -> 命题}
  证明: by
  simp only [ChartedSpace.liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · exact Topology.IsEmbedding.subtypeVal.isInducing.continuousWithinAt_iff.symm
  · rfl

Depends on / 依赖: ChartedSpace, ChartedSpace.liftPropWithinAt_iff, IsEmbedding, Topology, Topology.IsEmbedding.subtypeVal.isInducing.continuousWithinAt_iff.symm, congrm, continuousWithinAt_iff, isInducing, liftPropWithinAt_iff, subtypeVal
-/
lemma liftPropWithinAt_subtypeVal_comp_iff {P : (H -> H') -> Set H -> H -> Prop}
    {U : Opens M'} (f : M -> U) (s : Set M) (x : M) :
    LiftPropWithinAt P (Subtype.val ∘ f) s x ↔ LiftPropWithinAt P f s x := by
  simp only [ChartedSpace.liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · exact Topology.IsEmbedding.subtypeVal.isInducing.continuousWithinAt_iff.symm
  · rfl

end ChartedSpace

open ChartedSpace

namespace StructureGroupoid

variable {G : StructureGroupoid H} {G' : StructureGroupoid H'} {e e' : OpenPartialHomeomorph M H}
  {f f' : OpenPartialHomeomorph M' H'} {P : (H -> H') -> Set H -> H -> Prop} {g g' : M -> M'}
  {s t : Set M} {x : M} {Q : (H -> H) -> Set H -> H -> Prop}

/--
theorem `liftPropWithinAt_univ` / 定理 `liftPropWithinAt_univ`

English:
theorem liftPropWithinAt_univ
  statement: LiftPropWithinAt P g univ x ↔ LiftPropAt P g x
  proof: Iff.rfl

中文:
定理 liftPropWithinAt_univ
  结论: Lift命题WithinAt P g univ x ↔ Lift命题At P g x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem liftPropWithinAt_univ : LiftPropWithinAt P g univ x ↔ LiftPropAt P g x := Iff.rfl

/--
theorem `liftPropOn_univ` / 定理 `liftPropOn_univ`

English:
theorem liftPropOn_univ
  statement: LiftPropOn P g univ ↔ LiftProp P g
  proof: by
  simp [LiftPropOn, LiftProp, LiftPropAt]

中文:
定理 liftPropOn_univ
  结论: Lift命题On P g univ ↔ Lift命题 P g
  证明: by
  simp [LiftPropOn, LiftProp, LiftPropAt]

Depends on / 依赖: LiftProp, LiftPropAt, LiftPropOn
-/
theorem liftPropOn_univ : LiftPropOn P g univ ↔ LiftProp P g := by
  simp [LiftPropOn, LiftProp, LiftPropAt]

/--
theorem `liftPropWithinAt_self` / 定理 `liftPropWithinAt_self`

English:
theorem liftPropWithinAt_self
  given: {f : H -> H'} {s : Set H} {x : H}
  proof: liftPropWithinAt_iff' ..

中文:
定理 liftPropWithinAt_self
  条件: {f : H -> H'} {s : Set H} {x : H}
  证明: liftPropWithinAt_iff' ..

Depends on / 依赖: liftPropWithinAt_iff
-/
theorem liftPropWithinAt_self {f : H -> H'} {s : Set H} {x : H} :
    LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧ P f s x :=
  liftPropWithinAt_iff' ..

/--
theorem `liftPropWithinAt_self_source` / 定理 `liftPropWithinAt_self_source`

English:
theorem liftPropWithinAt_self_source
  given: {f : H -> M'} {s : Set H} {x : H}
  proof: liftPropWithinAt_iff' ..

中文:
定理 liftPropWithinAt_self_source
  条件: {f : H -> M'} {s : Set H} {x : H}
  证明: liftPropWithinAt_iff' ..

Depends on / 依赖: liftPropWithinAt_iff
-/
theorem liftPropWithinAt_self_source {f : H -> M'} {s : Set H} {x : H} :
    LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧ P (chartAt H' (f x) ∘ f) s x :=
  liftPropWithinAt_iff' ..

/--
theorem `liftPropWithinAt_self_target` / 定理 `liftPropWithinAt_self_target`

English:
theorem liftPropWithinAt_self_target
  given: {f : M -> H'}
  proof: liftPropWithinAt_iff' ..

中文:
定理 liftPropWithinAt_self_target
  条件: {f : M -> H'}
  证明: liftPropWithinAt_iff' ..

Depends on / 依赖: liftPropWithinAt_iff
-/
theorem liftPropWithinAt_self_target {f : M -> H'} :
    LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧
      P (f ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x) :=
  liftPropWithinAt_iff' ..

namespace LocalInvariantProp

section
variable (hG : G.LocalInvariantProp G' P)
include hG

/--
theorem `liftPropWithinAt_iff` / 定理 `liftPropWithinAt_iff`

English:
theorem liftPropWithinAt_iff
  given: {f : M -> M'}
  proof: by
  rw [liftPropWithinAt_iff']
  refine and_congr_right fun hf => hG.congr_set ?_
  exact OpenPartialHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter hf
    (mem_chart_source H x) (chart_source_mem_nhds H' (f x))

中文:
定理 liftPropWithinAt_iff
  条件: {f : M -> M'}
  证明: by
  rw [liftPropWithinAt_iff']
  refine and_congr_right fun hf => hG.congr_set ?_
  exact OpenPartialHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter hf
    (mem_chart_source H x) (chart_source_mem_nhds H' (f x))

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter, and_congr_right, chart_source_mem_nhds, congr_set, hG.congr_set, liftPropWithinAt_iff, mem_chart_source, preimage_eventuallyEq_target_inter_preimage_inter
-/
theorem liftPropWithinAt_iff {f : M -> M'} :
    LiftPropWithinAt P f s x ↔
      ContinuousWithinAt f s x ∧
        P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm)
          ((chartAt H x).target inter (chartAt H x).symm ⁻¹' (s inter f ⁻¹' (chartAt H' (f x)).source))
          (chartAt H x x) := by
  rw [liftPropWithinAt_iff']
  refine and_congr_right fun hf => hG.congr_set ?_
  exact OpenPartialHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter hf
    (mem_chart_source H x) (chart_source_mem_nhds H' (f x))

/--
theorem `liftPropWithinAt_indep_chart_source_aux` / 定理 `liftPropWithinAt_indep_chart_source_aux`

English:
theorem liftPropWithinAt_indep_chart_source_aux
  statement: (g : M -> H')
  proof: by
  rw [← hG.right_invariance (compatible_of_mem_maximalAtlas_right (x := x) he)]; swap
  · simp [xe]
  simp only [OpenPartialHomeomorph.trans_apply, mem_chart_source, OpenPartialHomeomorph.left_inv]
  apply hG.congr_set_fun
  · refine (eventually_of_mem ?_ fun y (hy : y in e.symm ⁻¹' (chartAt H x)

中文:
定理 liftPropWithinAt_indep_chart_source_aux
  结论: (g : M -> H')
  证明: by
  rw [← hG.right_invariance (compatible_of_mem_maximalAtlas_right (x := x) he)]; swap
  · simp [xe]
  simp only [OpenPartialHomeomorph.trans_apply, mem_chart_source, OpenPartialHomeomorph.left_inv]
  apply hG.congr_set_fun
  · refine (eventually_of_mem ?_ fun y (hy : y in e.symm ⁻¹' (chartAt H x)

Depends on / 依赖: OpenPartialHom, OpenPartialHomeomorph, OpenPartialHomeomorph.left_inv, OpenPartialHomeomorph.trans_apply, chartAt, compatible_of_mem_maximalAtlas_right, congr_set_fun, continuousAt, e.left_inv, e.mapsTo, e.symm, e.symm.continuousAt, eventually_of_mem, hG.congr_set_fun, hG.right_invariance, left_inv, mapsTo, mem_chart_source, mem_nhds, mem_preimage
-/
theorem liftPropWithinAt_indep_chart_source_aux (g : M -> H')
    (he : e in G.maximalAtlas M) (xe : x in e.source) :
    P (g ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x) ↔
      P (g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  rw [← hG.right_invariance (compatible_of_mem_maximalAtlas_right (x := x) he)]; swap
  · simp [xe]
  simp only [OpenPartialHomeomorph.trans_apply, mem_chart_source, OpenPartialHomeomorph.left_inv]
  apply hG.congr_set_fun
  · refine (eventually_of_mem ?_ fun y (hy : y in e.symm ⁻¹' (chartAt H x).source) => ?_).set_eq
    · refine (e.symm.continuousAt <| e.mapsTo xe).preimage_mem_nhds
        ((chartAt H x).open_source.mem_nhds ?_)
      simp_rw [e.left_inv xe, mem_chart_source H x]
    simp_rw [mem_preimage, OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
      Function.comp_apply, (chartAt H x).left_inv hy]
  · refine ((e.eventually_nhds' _ xe).mpr <| (chartAt H x).eventually_left_inverse
      (mem_chart_source H x)).mono fun y hy => ?_
    simp [hy]

/--
theorem `liftPropWithinAt_indep_chart_target_aux2` / 定理 `liftPropWithinAt_indep_chart_target_aux2`

English:
theorem liftPropWithinAt_indep_chart_target_aux2
  statement: (g : H -> M') {x : H} {s : Set H}
  proof: by
  have hcont : ContinuousWithinAt ((chartAt H' (g x)) ∘ g) s x :=
    ((chartAt H' (g x)).continuousAt (by simp)).comp_continuousWithinAt hgs
  rw [← hG.left_invariance (compatible_of_mem_maximalAtlas_right (x := g x) hf) hcont
      (by simp [xf]; rw [mfld_simps])]
  refine hG.congr_iff_nhdsWith

中文:
定理 liftPropWithinAt_indep_chart_target_aux2
  结论: (g : H -> M') {x : H} {s : Set H}
  证明: by
  have hcont : ContinuousWithinAt ((chartAt H' (g x)) ∘ g) s x :=
    ((chartAt H' (g x)).continuousAt (by simp)).comp_continuousWithinAt hgs
  rw [← hG.left_invariance (compatible_of_mem_maximalAtlas_right (x := g x) hf) hcont
      (by simp [xf]; rw [mfld_simps])]
  refine hG.congr_iff_nhdsWith

Depends on / 依赖: ContinuousWithinAt, chartAt, comp_continuousWithinAt, compatible_of_mem_maximalAtlas_right, congr_arg, congr_iff_nhdsWithin, continuousAt, eventually, eventually_left_inverse, hG.congr_iff_nhdsWithin, hG.left_invariance, hgs.eventually, left_invariance, mem_chart_source, mfld_simps
-/
theorem liftPropWithinAt_indep_chart_target_aux2 (g : H -> M') {x : H} {s : Set H}
    (hf : f in G'.maximalAtlas M')
    (xf : g x in f.source) (hgs : ContinuousWithinAt g s x) :
    P ((chartAt H' (g x)) ∘ g) s x ↔ P (f ∘ g) s x := by
  have hcont : ContinuousWithinAt ((chartAt H' (g x)) ∘ g) s x :=
    ((chartAt H' (g x)).continuousAt (by simp)).comp_continuousWithinAt hgs
  rw [← hG.left_invariance (compatible_of_mem_maximalAtlas_right (x := g x) hf) hcont
      (by simp [xf]; rw [mfld_simps])]
  refine hG.congr_iff_nhdsWithin ?_ (by simp)
  exact (hgs.eventually <| (chartAt H' (g x)).eventually_left_inverse
    (mem_chart_source H' (g x))).mono fun y => congr_arg f

/--
theorem `liftPropWithinAt_indep_chart_target_aux` / 定理 `liftPropWithinAt_indep_chart_target_aux`

English:
theorem liftPropWithinAt_indep_chart_target_aux
  statement: {g : X -> M'} {e : OpenPartialHomeomorph X H} {x : X}
  proof: by
  rw [← e.left_inv xe] at xf hgs
  rw [← hG.liftPropWithinAt_indep_chart_target_aux2 (g ∘ e.symm) hf xf]
  · simp [xe]
  · exact hgs.comp (e.symm.continuousAt <| e.mapsTo xe).continuousWithinAt Subset.rfl

中文:
定理 liftPropWithinAt_indep_chart_target_aux
  结论: {g : X -> M'} {e : OpenPartialHomeomorph X H} {x : X}
  证明: by
  rw [← e.left_inv xe] at xf hgs
  rw [← hG.liftPropWithinAt_indep_chart_target_aux2 (g ∘ e.symm) hf xf]
  · simp [xe]
  · exact hgs.comp (e.symm.continuousAt <| e.mapsTo xe).continuousWithinAt Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, continuousAt, continuousWithinAt, e.left_inv, e.mapsTo, e.symm, e.symm.continuousAt, hG.liftPropWithinAt_indep_chart_target_aux2, hgs.comp, left_inv, liftPropWithinAt_indep_chart_target_aux2, mapsTo
-/
theorem liftPropWithinAt_indep_chart_target_aux {g : X -> M'} {e : OpenPartialHomeomorph X H} {x : X}
    {s : Set X} (xe : x in e.source)
    (hf : f in G'.maximalAtlas M') (xf : g x in f.source) (hgs : ContinuousWithinAt g s x) :
    P ((chartAt H' (g x)) ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x)
      ↔ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  rw [← e.left_inv xe] at xf hgs
  rw [← hG.liftPropWithinAt_indep_chart_target_aux2 (g ∘ e.symm) hf xf]
  · simp [xe]
  · exact hgs.comp (e.symm.continuousAt <| e.mapsTo xe).continuousWithinAt Subset.rfl

/--
theorem `liftPropWithinAt_indep_chart_aux'` / 定理 `liftPropWithinAt_indep_chart_aux'`

English:
theorem liftPropWithinAt_indep_chart_aux'
  statement: (he : e in G.maximalAtlas M) (xe : x in e.source)
  proof: by
  rw [← Function.comp_assoc]; rw [hG.liftPropWithinAt_indep_chart_source_aux ((chartAt H' (g x)) ∘ g) he xe]; rw [Function.comp_assoc]; rw [hG.liftPropWithinAt_indep_chart_target_aux xe hf xf hgs]

中文:
定理 liftPropWithinAt_indep_chart_aux'
  结论: (he : e in G.maximalAtlas M) (xe : x in e.source)
  证明: by
  rw [← Function.comp_assoc]; rw [hG.liftPropWithinAt_indep_chart_source_aux ((chartAt H' (g x)) ∘ g) he xe]; rw [Function.comp_assoc]; rw [hG.liftPropWithinAt_indep_chart_target_aux xe hf xf hgs]

Depends on / 依赖: Function, Function.comp_assoc, chartAt, comp_assoc, hG.liftPropWithinAt_indep_chart_source_aux, hG.liftPropWithinAt_indep_chart_target_aux, liftPropWithinAt_indep_chart_source_aux, liftPropWithinAt_indep_chart_target_aux
-/
theorem liftPropWithinAt_indep_chart_aux' (he : e in G.maximalAtlas M) (xe : x in e.source)
    (hf : f in G'.maximalAtlas M') (xf : g x in f.source)
    (hgs : ContinuousWithinAt g s x) :
    P ((chartAt H' (g x)) ∘ g ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x)
      ↔ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  rw [← Function.comp_assoc]; rw [hG.liftPropWithinAt_indep_chart_source_aux ((chartAt H' (g x)) ∘ g) he xe]; rw [Function.comp_assoc]; rw [hG.liftPropWithinAt_indep_chart_target_aux xe hf xf hgs]

/--
theorem `liftPropWithinAt_indep_chart_aux` / 定理 `liftPropWithinAt_indep_chart_aux`

English:
theorem liftPropWithinAt_indep_chart_aux
  statement: (he : e in G.maximalAtlas M) (xe : x in e.source)
  proof: by
  rw [← liftPropWithinAt_indep_chart_aux' hG he' xe' hf' xf' hgs]; rw [liftPropWithinAt_indep_chart_aux' hG he xe hf xf hgs]

中文:
定理 liftPropWithinAt_indep_chart_aux
  结论: (he : e in G.maximalAtlas M) (xe : x in e.source)
  证明: by
  rw [← liftPropWithinAt_indep_chart_aux' hG he' xe' hf' xf' hgs]; rw [liftPropWithinAt_indep_chart_aux' hG he xe hf xf hgs]

Depends on / 依赖: liftPropWithinAt_indep_chart_aux
-/
theorem liftPropWithinAt_indep_chart_aux (he : e in G.maximalAtlas M) (xe : x in e.source)
    (he' : e' in G.maximalAtlas M) (xe' : x in e'.source) (hf : f in G'.maximalAtlas M')
    (xf : g x in f.source) (hf' : f' in G'.maximalAtlas M') (xf' : g x in f'.source)
    (hgs : ContinuousWithinAt g s x) :
    P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P (f' ∘ g ∘ e'.symm) (e'.symm ⁻¹' s) (e' x) := by
  rw [← liftPropWithinAt_indep_chart_aux' hG he' xe' hf' xf' hgs]; rw [liftPropWithinAt_indep_chart_aux' hG he xe hf xf hgs]

/--
theorem `liftPropWithinAt_indep_chart` / 定理 `liftPropWithinAt_indep_chart`

English:
theorem liftPropWithinAt_indep_chart
  proof: by
  simp only [liftPropWithinAt_iff']
exact and_congr_right fun h => hG.liftPropWithinAt_indep_chart_aux' he xe hf xf h

中文:
定理 liftPropWithinAt_indep_chart
  证明: by
  simp only [liftPropWithinAt_iff']
exact and_congr_right fun h => hG.liftPropWithinAt_indep_chart_aux' he xe hf xf h

Depends on / 依赖: and_congr_right, hG.liftPropWithinAt_indep_chart_aux, liftPropWithinAt_iff, liftPropWithinAt_indep_chart_aux
-/
theorem liftPropWithinAt_indep_chart
    (he : e in G.maximalAtlas M) (xe : x in e.source) (hf : f in G'.maximalAtlas M')
    (xf : g x in f.source) :
    LiftPropWithinAt P g s x ↔
    ContinuousWithinAt g s x ∧ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  simp only [liftPropWithinAt_iff']
exact and_congr_right fun h => hG.liftPropWithinAt_indep_chart_aux' he xe hf xf h

/--
theorem `liftPropWithinAt_indep_chart_source` / 定理 `liftPropWithinAt_indep_chart_source`

English:
theorem liftPropWithinAt_indep_chart_source
  given: (he : e in G.maximalAtlas M) (xe : x in e.source)
  proof: by
  rw [liftPropWithinAt_self_source]; rw [liftPropWithinAt_iff']; rw [e.symm.continuousWithinAt_iff_continuousWithinAt_comp_right xe]; rw [e.symm_symm]
  refine and_congr Iff.rfl ?_
  rw [Function.comp_apply]; rw [e.left_inv xe]; rw [← Function.comp_assoc]; rw [hG.liftPropWithinAt_indep_chart_sour

中文:
定理 liftPropWithinAt_indep_chart_source
  条件: (he : e in G.maximalAtlas M) (xe : x in e.source)
  证明: by
  rw [liftPropWithinAt_self_source]; rw [liftPropWithinAt_iff']; rw [e.symm.continuousWithinAt_iff_continuousWithinAt_comp_right xe]; rw [e.symm_symm]
  refine and_congr Iff.rfl ?_
  rw [Function.comp_apply]; rw [e.left_inv xe]; rw [← Function.comp_assoc]; rw [hG.liftPropWithinAt_indep_chart_sour

Depends on / 依赖: Function, Function.comp_apply, Function.comp_assoc, Iff.rfl, and_congr, chartAt, comp_apply, comp_assoc, continuousWithinAt_iff_continuousWithinAt_comp_right, e.left_inv, e.symm.continuousWithinAt_iff_continuousWithinAt_comp_right, e.symm_symm, hG.liftPropWithinAt_indep_chart_source_aux, left_inv, liftPropWithinAt_iff, liftPropWithinAt_indep_chart_source_aux, liftPropWithinAt_self_source, symm_symm
-/
theorem liftPropWithinAt_indep_chart_source (he : e in G.maximalAtlas M) (xe : x in e.source) :
    LiftPropWithinAt P g s x ↔ LiftPropWithinAt P (g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  rw [liftPropWithinAt_self_source]; rw [liftPropWithinAt_iff']; rw [e.symm.continuousWithinAt_iff_continuousWithinAt_comp_right xe]; rw [e.symm_symm]
  refine and_congr Iff.rfl ?_
  rw [Function.comp_apply]; rw [e.left_inv xe]; rw [← Function.comp_assoc]; rw [hG.liftPropWithinAt_indep_chart_source_aux (chartAt _ (g x) ∘ g) he xe]; rw [Function.comp_assoc]

/--
theorem `liftPropWithinAt_indep_chart_target` / 定理 `liftPropWithinAt_indep_chart_target`

English:
theorem liftPropWithinAt_indep_chart_target
  statement: (hf : f in G'.maximalAtlas M')
  proof: by
  rw [liftPropWithinAt_self_target]; rw [liftPropWithinAt_iff']; rw [and_congr_right_iff]
  intro hg
  simp_rw [(f.continuousAt xf).comp_continuousWithinAt hg, true_and]
  exact hG.liftPropWithinAt_indep_chart_target_aux (mem_chart_source _ _) hf xf hg

中文:
定理 liftPropWithinAt_indep_chart_target
  结论: (hf : f in G'.maximalAtlas M')
  证明: by
  rw [liftPropWithinAt_self_target]; rw [liftPropWithinAt_iff']; rw [and_congr_right_iff]
  intro hg
  simp_rw [(f.continuousAt xf).comp_continuousWithinAt hg, true_and]
  exact hG.liftPropWithinAt_indep_chart_target_aux (mem_chart_source _ _) hf xf hg

Depends on / 依赖: and_congr_right_iff, comp_continuousWithinAt, continuousAt, f.continuousAt, hG.liftPropWithinAt_indep_chart_target_aux, liftPropWithinAt_iff, liftPropWithinAt_indep_chart_target_aux, liftPropWithinAt_self_target, mem_chart_source, simp_rw, true_and
-/
theorem liftPropWithinAt_indep_chart_target (hf : f in G'.maximalAtlas M')
    (xf : g x in f.source) :
    LiftPropWithinAt P g s x ↔ ContinuousWithinAt g s x ∧ LiftPropWithinAt P (f ∘ g) s x := by
  rw [liftPropWithinAt_self_target]; rw [liftPropWithinAt_iff']; rw [and_congr_right_iff]
  intro hg
  simp_rw [(f.continuousAt xf).comp_continuousWithinAt hg, true_and]
  exact hG.liftPropWithinAt_indep_chart_target_aux (mem_chart_source _ _) hf xf hg

/--
theorem `liftPropWithinAt_indep_chart'` / 定理 `liftPropWithinAt_indep_chart'`

English:
theorem liftPropWithinAt_indep_chart'
  proof: by
  rw [hG.liftPropWithinAt_indep_chart he xe hf xf]; rw [liftPropWithinAt_self]; rw [and_left_comm]; rw [Iff.comm]; rw [and_iff_right_iff_imp]
  intro h
  have h1 := (e.symm.continuousWithinAt_iff_continuousWithinAt_comp_right xe).mp h.1
  have : ContinuousAt f ((g ∘ e.symm) (e x)) := by
    simp_

中文:
定理 liftPropWithinAt_indep_chart'
  证明: by
  rw [hG.liftPropWithinAt_indep_chart he xe hf xf]; rw [liftPropWithinAt_self]; rw [and_left_comm]; rw [Iff.comm]; rw [and_iff_right_iff_imp]
  intro h
  have h1 := (e.symm.continuousWithinAt_iff_continuousWithinAt_comp_right xe).mp h.1
  have : ContinuousAt f ((g ∘ e.symm) (e x)) := by
    simp_

Depends on / 依赖: ContinuousAt, Function, Function.comp, Iff.comm, and_iff_right_iff_imp, and_left_comm, comp_continuousWithinAt, continuousAt, continuousWithinAt_iff_continuousWithinAt_comp_right, e.left_inv, e.symm, e.symm.continuousWithinAt_iff_continuousWithinAt_comp_right, f.continuousAt, hG.liftPropWithinAt_indep_chart, left_inv, liftPropWithinAt_indep_chart, liftPropWithinAt_self, simp_rw, this.comp_continuousWithinAt
-/
theorem liftPropWithinAt_indep_chart'
    (he : e in G.maximalAtlas M) (xe : x in e.source) (hf : f in G'.maximalAtlas M')
    (xf : g x in f.source) :
    LiftPropWithinAt P g s x ↔
      ContinuousWithinAt g s x ∧ LiftPropWithinAt P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  rw [hG.liftPropWithinAt_indep_chart he xe hf xf]; rw [liftPropWithinAt_self]; rw [and_left_comm]; rw [Iff.comm]; rw [and_iff_right_iff_imp]
  intro h
  have h1 := (e.symm.continuousWithinAt_iff_continuousWithinAt_comp_right xe).mp h.1
  have : ContinuousAt f ((g ∘ e.symm) (e x)) := by
    simp_rw [Function.comp, e.left_inv xe, f.continuousAt xf]
  exact this.comp_continuousWithinAt h1

/--
theorem `liftPropOn_indep_chart` / 定理 `liftPropOn_indep_chart`

English:
theorem liftPropOn_indep_chart
  statement: (he : e in G.maximalAtlas M)
  proof: by
  convert! ((hG.liftPropWithinAt_indep_chart he (e.mapsTo_symm hy.1) hf hy.2.2).1 (h _ hy.2.1)).2
  rw [e.right_inv hy.1]

中文:
定理 liftPropOn_indep_chart
  结论: (he : e in G.maximalAtlas M)
  证明: by
  convert! ((hG.liftPropWithinAt_indep_chart he (e.mapsTo_symm hy.1) hf hy.2.2).1 (h _ hy.2.1)).2
  rw [e.right_inv hy.1]

Depends on / 依赖: convert, e.mapsTo_symm, e.right_inv, hG.liftPropWithinAt_indep_chart, liftPropWithinAt_indep_chart, mapsTo_symm, right_inv
-/
theorem liftPropOn_indep_chart (he : e in G.maximalAtlas M)
    (hf : f in G'.maximalAtlas M') (h : LiftPropOn P g s) {y : H}
    (hy : y in e.target inter e.symm ⁻¹' (s inter g ⁻¹' f.source)) :
    P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) y := by
  convert! ((hG.liftPropWithinAt_indep_chart he (e.mapsTo_symm hy.1) hf hy.2.2).1 (h _ hy.2.1)).2
  rw [e.right_inv hy.1]

/--
theorem `liftPropWithinAt_inter'` / 定理 `liftPropWithinAt_inter'`

English:
theorem liftPropWithinAt_inter'
  given: (ht : t in 𝓝[s] x)
  proof: by
  rw [liftPropWithinAt_iff']; rw [liftPropWithinAt_iff']; rw [continuousWithinAt_inter' ht]; rw [hG.congr_set]
  simp_rw [eventuallyEq_set, mem_preimage,
    (chartAt _ x).eventually_nhds' (fun x => x in s inter t ↔ x in s) (mem_chart_source _ x)]
  exact (mem_nhdsWithin_iff_eventuallyEq.mp ht).s

中文:
定理 liftPropWithinAt_inter'
  条件: (ht : t in 𝓝[s] x)
  证明: by
  rw [liftPropWithinAt_iff']; rw [liftPropWithinAt_iff']; rw [continuousWithinAt_inter' ht]; rw [hG.congr_set]
  simp_rw [eventuallyEq_set, mem_preimage,
    (chartAt _ x).eventually_nhds' (fun x => x in s inter t ↔ x in s) (mem_chart_source _ x)]
  exact (mem_nhdsWithin_iff_eventuallyEq.mp ht).s

Depends on / 依赖: chartAt, congr_set, continuousWithinAt_inter, eventuallyEq_set, eventually_nhds, hG.congr_set, liftPropWithinAt_iff, mem_chart_source, mem_iff, mem_nhdsWithin_iff_eventuallyEq, mem_nhdsWithin_iff_eventuallyEq.mp, mem_preimage, simp_rw, symm.mem_iff
-/
theorem liftPropWithinAt_inter' (ht : t in 𝓝[s] x) :
    LiftPropWithinAt P g (s inter t) x ↔ LiftPropWithinAt P g s x := by
  rw [liftPropWithinAt_iff']; rw [liftPropWithinAt_iff']; rw [continuousWithinAt_inter' ht]; rw [hG.congr_set]
  simp_rw [eventuallyEq_set, mem_preimage,
    (chartAt _ x).eventually_nhds' (fun x => x in s inter t ↔ x in s) (mem_chart_source _ x)]
  exact (mem_nhdsWithin_iff_eventuallyEq.mp ht).symm.mem_iff

/--
theorem `liftPropWithinAt_inter` / 定理 `liftPropWithinAt_inter`

English:
theorem liftPropWithinAt_inter
  given: (ht : t in 𝓝 x)
  proof: hG.liftPropWithinAt_inter' (mem_nhdsWithin_of_mem_nhds ht)

中文:
定理 liftPropWithinAt_inter
  条件: (ht : t in 𝓝 x)
  证明: hG.liftPropWithinAt_inter' (mem_nhdsWithin_of_mem_nhds ht)

Depends on / 依赖: hG.liftPropWithinAt_inter, liftPropWithinAt_inter, mem_nhdsWithin_of_mem_nhds
-/
theorem liftPropWithinAt_inter (ht : t in 𝓝 x) :
    LiftPropWithinAt P g (s inter t) x ↔ LiftPropWithinAt P g s x :=
  hG.liftPropWithinAt_inter' (mem_nhdsWithin_of_mem_nhds ht)

/--
theorem `liftPropWithinAt_congr_set` / 定理 `liftPropWithinAt_congr_set`

English:
theorem liftPropWithinAt_congr_set
  given: (hu : s =ᶠ[𝓝 x] t)
  proof: by
  rw [← hG.liftPropWithinAt_inter (s := s) hu]; rw [← hG.liftPropWithinAt_inter (s := t) hu]; rw [← eq_iff_iff]
  congr 1
  aesop

中文:
定理 liftPropWithinAt_congr_set
  条件: (hu : s =ᶠ[𝓝 x] t)
  证明: by
  rw [← hG.liftPropWithinAt_inter (s := s) hu]; rw [← hG.liftPropWithinAt_inter (s := t) hu]; rw [← eq_iff_iff]
  congr 1
  aesop

Depends on / 依赖: eq_iff_iff, hG.liftPropWithinAt_inter, liftPropWithinAt_inter
-/
theorem liftPropWithinAt_congr_set (hu : s =ᶠ[𝓝 x] t) :
    LiftPropWithinAt P g s x ↔ LiftPropWithinAt P g t x := by
  rw [← hG.liftPropWithinAt_inter (s := s) hu]; rw [← hG.liftPropWithinAt_inter (s := t) hu]; rw [← eq_iff_iff]
  congr 1
  aesop

/--
theorem `liftPropAt_of_liftPropWithinAt` / 定理 `liftPropAt_of_liftPropWithinAt`

English:
theorem liftPropAt_of_liftPropWithinAt
  given: (h : LiftPropWithinAt P g s x) (hs : s in 𝓝 x)
  proof: by
  rwa [← univ_inter s, hG.liftPropWithinAt_inter hs] at h

中文:
定理 liftPropAt_of_liftPropWithinAt
  条件: (h : Lift命题WithinAt P g s x) (hs : s in 𝓝 x)
  证明: by
  rwa [← univ_inter s, hG.liftPropWithinAt_inter hs] at h

Depends on / 依赖: hG.liftPropWithinAt_inter, liftPropWithinAt_inter, univ_inter
-/
theorem liftPropAt_of_liftPropWithinAt (h : LiftPropWithinAt P g s x) (hs : s in 𝓝 x) :
    LiftPropAt P g x := by
  rwa [← univ_inter s, hG.liftPropWithinAt_inter hs] at h

/--
theorem `liftPropWithinAt_of_liftPropAt_of_mem_nhds` / 定理 `liftPropWithinAt_of_liftPropAt_of_mem_nhds`

English:
theorem liftPropWithinAt_of_liftPropAt_of_mem_nhds
  given: (h : LiftPropAt P g x) (hs : s in 𝓝 x)
  proof: by
  rwa [← univ_inter s, hG.liftPropWithinAt_inter hs]

中文:
定理 liftPropWithinAt_of_liftPropAt_of_mem_nhds
  条件: (h : Lift命题At P g x) (hs : s in 𝓝 x)
  证明: by
  rwa [← univ_inter s, hG.liftPropWithinAt_inter hs]

Depends on / 依赖: hG.liftPropWithinAt_inter, liftPropWithinAt_inter, univ_inter
-/
theorem liftPropWithinAt_of_liftPropAt_of_mem_nhds (h : LiftPropAt P g x) (hs : s in 𝓝 x) :
    LiftPropWithinAt P g s x := by
  rwa [← univ_inter s, hG.liftPropWithinAt_inter hs]

/--
theorem `liftPropOn_of_locally_liftPropOn` / 定理 `liftPropOn_of_locally_liftPropOn`

English:
theorem liftPropOn_of_locally_liftPropOn
  proof: by
  intro x hx
  rcases h x hx with ⟨u, u_open, xu, hu⟩
  have := hu x ⟨hx, xu⟩
  rwa [hG.liftPropWithinAt_inter] at this
  exact u_open.mem_nhds xu

中文:
定理 liftPropOn_of_locally_liftPropOn
  证明: by
  intro x hx
  rcases h x hx with ⟨u, u_open, xu, hu⟩
  have := hu x ⟨hx, xu⟩
  rwa [hG.liftPropWithinAt_inter] at this
  exact u_open.mem_nhds xu

Depends on / 依赖: hG.liftPropWithinAt_inter, liftPropWithinAt_inter, mem_nhds, u_open, u_open.mem_nhds
-/
theorem liftPropOn_of_locally_liftPropOn
    (h : forall x in s, exists u, IsOpen u ∧ x in u ∧ LiftPropOn P g (s inter u)) : LiftPropOn P g s := by
  intro x hx
  rcases h x hx with ⟨u, u_open, xu, hu⟩
  have := hu x ⟨hx, xu⟩
  rwa [hG.liftPropWithinAt_inter] at this
  exact u_open.mem_nhds xu

/--
theorem `liftProp_of_locally_liftPropOn` / 定理 `liftProp_of_locally_liftPropOn`

English:
theorem liftProp_of_locally_liftPropOn
  given: (h : forall x, exists u, IsOpen u ∧ x in u ∧ LiftPropOn P g u)
  proof: by
  rw [← liftPropOn_univ]
  refine hG.liftPropOn_of_locally_liftPropOn fun x _ => ?_
  simp [h x]

中文:
定理 liftProp_of_locally_liftPropOn
  条件: (h : 对任意 x, 存在 u, IsOpen u ∧ x in u ∧ Lift命题On P g u)
  证明: by
  rw [← liftPropOn_univ]
  refine hG.liftPropOn_of_locally_liftPropOn fun x _ => ?_
  simp [h x]

Depends on / 依赖: hG.liftPropOn_of_locally_liftPropOn, liftPropOn_of_locally_liftPropOn, liftPropOn_univ
-/
theorem liftProp_of_locally_liftPropOn (h : forall x, exists u, IsOpen u ∧ x in u ∧ LiftPropOn P g u) :
    LiftProp P g := by
  rw [← liftPropOn_univ]
  refine hG.liftPropOn_of_locally_liftPropOn fun x _ => ?_
  simp [h x]

/--
theorem `liftPropWithinAt_congr_of_eventuallyEq` / 定理 `liftPropWithinAt_congr_of_eventuallyEq`

English:
theorem liftPropWithinAt_congr_of_eventuallyEq
  statement: (h : LiftPropWithinAt P g s x) (h₁ : g' =ᶠ[𝓝[s] x] g)
  proof: by
  refine ⟨h.1.congr_of_eventuallyEq h₁ hx, ?_⟩
  refine hG.congr_nhdsWithin' ?_
    (by simp_rw [Function.comp_apply, (chartAt H x).left_inv (mem_chart_source H x), hx]) h.2
  simp_rw [EventuallyEq, Function.comp_apply]
  rw [(chartAt H x).eventually_nhdsWithin'
    (fun y => chartAt H' (g' x) (g

中文:
定理 liftPropWithinAt_congr_of_eventuallyEq
  结论: (h : Lift命题WithinAt P g s x) (h₁ : g' =ᶠ[𝓝[s] x] g)
  证明: by
  refine ⟨h.1.congr_of_eventuallyEq h₁ hx, ?_⟩
  refine hG.congr_nhdsWithin' ?_
    (by simp_rw [Function.comp_apply, (chartAt H x).left_inv (mem_chart_source H x), hx]) h.2
  simp_rw [EventuallyEq, Function.comp_apply]
  rw [(chartAt H x).eventually_nhdsWithin'
    (fun y => chartAt H' (g' x) (g

Depends on / 依赖: EventuallyEq, Function, Function.comp_apply, chartAt, comp_apply, congr_nhdsWithin, congr_of_eventuallyEq, eventually_nhdsWithin, hG.congr_nhdsWithin, left_inv, mem_chart_source, simp_rw
-/
theorem liftPropWithinAt_congr_of_eventuallyEq (h : LiftPropWithinAt P g s x) (h₁ : g' =ᶠ[𝓝[s] x] g)
    (hx : g' x = g x) : LiftPropWithinAt P g' s x := by
  refine ⟨h.1.congr_of_eventuallyEq h₁ hx, ?_⟩
  refine hG.congr_nhdsWithin' ?_
    (by simp_rw [Function.comp_apply, (chartAt H x).left_inv (mem_chart_source H x), hx]) h.2
  simp_rw [EventuallyEq, Function.comp_apply]
  rw [(chartAt H x).eventually_nhdsWithin'
    (fun y => chartAt H' (g' x) (g' y) = chartAt H' (g x) (g y)) (mem_chart_source H x)]
  exact h₁.mono fun y hy => by rw [hx, hy]

/--
theorem `liftPropWithinAt_congr_of_eventuallyEq_of_mem` / 定理 `liftPropWithinAt_congr_of_eventuallyEq_of_mem`

English:
theorem liftPropWithinAt_congr_of_eventuallyEq_of_mem
  statement: (h : LiftPropWithinAt P g s x)
  proof: liftPropWithinAt_congr_of_eventuallyEq hG h h₁ (mem_of_mem_nhdsWithin h₂ h₁ :)

中文:
定理 liftPropWithinAt_congr_of_eventuallyEq_of_mem
  结论: (h : Lift命题WithinAt P g s x)
  证明: liftPropWithinAt_congr_of_eventuallyEq hG h h₁ (mem_of_mem_nhdsWithin h₂ h₁ :)

Depends on / 依赖: liftPropWithinAt_congr_of_eventuallyEq, mem_of_mem_nhdsWithin
-/
theorem liftPropWithinAt_congr_of_eventuallyEq_of_mem (h : LiftPropWithinAt P g s x)
    (h₁ : g' =ᶠ[𝓝[s] x] g) (h₂ : x in s) : LiftPropWithinAt P g' s x :=
  liftPropWithinAt_congr_of_eventuallyEq hG h h₁ (mem_of_mem_nhdsWithin h₂ h₁ :)

/--
theorem `liftPropWithinAt_congr_iff_of_eventuallyEq` / 定理 `liftPropWithinAt_congr_iff_of_eventuallyEq`

English:
theorem liftPropWithinAt_congr_iff_of_eventuallyEq
  given: (h₁ : g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x)
  proof: ⟨fun h => hG.liftPropWithinAt_congr_of_eventuallyEq h h₁.symm hx.symm,
    fun h => hG.liftPropWithinAt_congr_of_eventuallyEq h h₁ hx⟩

中文:
定理 liftPropWithinAt_congr_iff_of_eventuallyEq
  条件: (h₁ : g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x)
  证明: ⟨fun h => hG.liftPropWithinAt_congr_of_eventuallyEq h h₁.symm hx.symm,
    fun h => hG.liftPropWithinAt_congr_of_eventuallyEq h h₁ hx⟩

Depends on / 依赖: hG.liftPropWithinAt_congr_of_eventuallyEq, hx.symm, liftPropWithinAt_congr_of_eventuallyEq
-/
theorem liftPropWithinAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) :
    LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x :=
  ⟨fun h => hG.liftPropWithinAt_congr_of_eventuallyEq h h₁.symm hx.symm,
    fun h => hG.liftPropWithinAt_congr_of_eventuallyEq h h₁ hx⟩

/--
theorem `liftPropWithinAt_congr_iff` / 定理 `liftPropWithinAt_congr_iff`

English:
theorem liftPropWithinAt_congr_iff
  given: (h₁ : forall y in s, g' y = g y) (hx : g' x = g x)
  proof: hG.liftPropWithinAt_congr_iff_of_eventuallyEq (eventually_nhdsWithin_of_forall h₁) hx

中文:
定理 liftPropWithinAt_congr_iff
  条件: (h₁ : 对任意 y in s, g' y = g y) (hx : g' x = g x)
  证明: hG.liftPropWithinAt_congr_iff_of_eventuallyEq (eventually_nhdsWithin_of_forall h₁) hx

Depends on / 依赖: eventually_nhdsWithin_of_forall, hG.liftPropWithinAt_congr_iff_of_eventuallyEq, liftPropWithinAt_congr_iff_of_eventuallyEq
-/
theorem liftPropWithinAt_congr_iff (h₁ : forall y in s, g' y = g y) (hx : g' x = g x) :
    LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x :=
  hG.liftPropWithinAt_congr_iff_of_eventuallyEq (eventually_nhdsWithin_of_forall h₁) hx

/--
theorem `liftPropWithinAt_congr_iff_of_mem` / 定理 `liftPropWithinAt_congr_iff_of_mem`

English:
theorem liftPropWithinAt_congr_iff_of_mem
  given: (h₁ : forall y in s, g' y = g y) (hx : x in s)
  proof: hG.liftPropWithinAt_congr_iff_of_eventuallyEq (eventually_nhdsWithin_of_forall h₁) (h₁ _ hx)

中文:
定理 liftPropWithinAt_congr_iff_of_mem
  条件: (h₁ : 对任意 y in s, g' y = g y) (hx : x in s)
  证明: hG.liftPropWithinAt_congr_iff_of_eventuallyEq (eventually_nhdsWithin_of_forall h₁) (h₁ _ hx)

Depends on / 依赖: eventually_nhdsWithin_of_forall, hG.liftPropWithinAt_congr_iff_of_eventuallyEq, liftPropWithinAt_congr_iff_of_eventuallyEq
-/
theorem liftPropWithinAt_congr_iff_of_mem (h₁ : forall y in s, g' y = g y) (hx : x in s) :
    LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x :=
  hG.liftPropWithinAt_congr_iff_of_eventuallyEq (eventually_nhdsWithin_of_forall h₁) (h₁ _ hx)

/--
theorem `liftPropWithinAt_congr` / 定理 `liftPropWithinAt_congr`

English:
theorem liftPropWithinAt_congr
  statement: (h : LiftPropWithinAt P g s x) (h₁ : forall y in s, g' y = g y)
  proof: (hG.liftPropWithinAt_congr_iff h₁ hx).mpr h

中文:
定理 liftPropWithinAt_congr
  结论: (h : Lift命题WithinAt P g s x) (h₁ : 对任意 y in s, g' y = g y)
  证明: (hG.liftPropWithinAt_congr_iff h₁ hx).mpr h

Depends on / 依赖: hG.liftPropWithinAt_congr_iff, liftPropWithinAt_congr_iff
-/
theorem liftPropWithinAt_congr (h : LiftPropWithinAt P g s x) (h₁ : forall y in s, g' y = g y)
    (hx : g' x = g x) : LiftPropWithinAt P g' s x :=
  (hG.liftPropWithinAt_congr_iff h₁ hx).mpr h

/--
theorem `liftPropWithinAt_congr_of_mem` / 定理 `liftPropWithinAt_congr_of_mem`

English:
theorem liftPropWithinAt_congr_of_mem
  statement: (h : LiftPropWithinAt P g s x) (h₁ : forall y in s, g' y = g y)
  proof: (hG.liftPropWithinAt_congr_iff h₁ (h₁ _ hx)).mpr h

中文:
定理 liftPropWithinAt_congr_of_mem
  结论: (h : Lift命题WithinAt P g s x) (h₁ : 对任意 y in s, g' y = g y)
  证明: (hG.liftPropWithinAt_congr_iff h₁ (h₁ _ hx)).mpr h

Depends on / 依赖: hG.liftPropWithinAt_congr_iff, liftPropWithinAt_congr_iff
-/
theorem liftPropWithinAt_congr_of_mem (h : LiftPropWithinAt P g s x) (h₁ : forall y in s, g' y = g y)
    (hx : x in s) : LiftPropWithinAt P g' s x :=
  (hG.liftPropWithinAt_congr_iff h₁ (h₁ _ hx)).mpr h

/--
theorem `liftPropAt_congr_iff_of_eventuallyEq` / 定理 `liftPropAt_congr_iff_of_eventuallyEq`

English:
theorem liftPropAt_congr_iff_of_eventuallyEq
  given: (h₁ : g' =ᶠ[𝓝 x] g)
  proof: hG.liftPropWithinAt_congr_iff_of_eventuallyEq (by simp_rw [nhdsWithin_univ, h₁]) h₁.eq_of_nhds

中文:
定理 liftPropAt_congr_iff_of_eventuallyEq
  条件: (h₁ : g' =ᶠ[𝓝 x] g)
  证明: hG.liftPropWithinAt_congr_iff_of_eventuallyEq (by simp_rw [nhdsWithin_univ, h₁]) h₁.eq_of_nhds

Depends on / 依赖: eq_of_nhds, hG.liftPropWithinAt_congr_iff_of_eventuallyEq, liftPropWithinAt_congr_iff_of_eventuallyEq, nhdsWithin_univ, simp_rw
-/
theorem liftPropAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝 x] g) :
    LiftPropAt P g' x ↔ LiftPropAt P g x :=
  hG.liftPropWithinAt_congr_iff_of_eventuallyEq (by simp_rw [nhdsWithin_univ, h₁]) h₁.eq_of_nhds

/--
theorem `liftPropAt_congr_of_eventuallyEq` / 定理 `liftPropAt_congr_of_eventuallyEq`

English:
theorem liftPropAt_congr_of_eventuallyEq
  given: (h : LiftPropAt P g x) (h₁ : g' =ᶠ[𝓝 x] g)
  proof: (hG.liftPropAt_congr_iff_of_eventuallyEq h₁).mpr h

中文:
定理 liftPropAt_congr_of_eventuallyEq
  条件: (h : Lift命题At P g x) (h₁ : g' =ᶠ[𝓝 x] g)
  证明: (hG.liftPropAt_congr_iff_of_eventuallyEq h₁).mpr h

Depends on / 依赖: hG.liftPropAt_congr_iff_of_eventuallyEq, liftPropAt_congr_iff_of_eventuallyEq
-/
theorem liftPropAt_congr_of_eventuallyEq (h : LiftPropAt P g x) (h₁ : g' =ᶠ[𝓝 x] g) :
    LiftPropAt P g' x :=
  (hG.liftPropAt_congr_iff_of_eventuallyEq h₁).mpr h

/--
theorem `liftPropOn_congr` / 定理 `liftPropOn_congr`

English:
theorem liftPropOn_congr
  given: (h : LiftPropOn P g s) (h₁ : forall y in s, g' y = g y)
  statement: LiftPropOn P g' s
  proof: fun x hx => hG.liftPropWithinAt_congr (h x hx) h₁ (h₁ x hx)

中文:
定理 liftPropOn_congr
  条件: (h : Lift命题On P g s) (h₁ : 对任意 y in s, g' y = g y)
  结论: Lift命题On P g' s
  证明: fun x hx => hG.liftPropWithinAt_congr (h x hx) h₁ (h₁ x hx)

Depends on / 依赖: hG.liftPropWithinAt_congr, liftPropWithinAt_congr
-/
theorem liftPropOn_congr (h : LiftPropOn P g s) (h₁ : forall y in s, g' y = g y) : LiftPropOn P g' s :=
  fun x hx => hG.liftPropWithinAt_congr (h x hx) h₁ (h₁ x hx)

/--
theorem `liftPropOn_congr_iff` / 定理 `liftPropOn_congr_iff`

English:
theorem liftPropOn_congr_iff
  given: (h₁ : forall y in s, g' y = g y)
  statement: LiftPropOn P g' s ↔ LiftPropOn P g s
  proof: ⟨fun h => hG.liftPropOn_congr h fun y hy => (h₁ y hy).symm, fun h => hG.liftPropOn_congr h h₁⟩

中文:
定理 liftPropOn_congr_iff
  条件: (h₁ : 对任意 y in s, g' y = g y)
  结论: Lift命题On P g' s ↔ Lift命题On P g s
  证明: ⟨fun h => hG.liftPropOn_congr h fun y hy => (h₁ y hy).symm, fun h => hG.liftPropOn_congr h h₁⟩

Depends on / 依赖: hG.liftPropOn_congr, liftPropOn_congr
-/
theorem liftPropOn_congr_iff (h₁ : forall y in s, g' y = g y) : LiftPropOn P g' s ↔ LiftPropOn P g s :=
  ⟨fun h => hG.liftPropOn_congr h fun y hy => (h₁ y hy).symm, fun h => hG.liftPropOn_congr h h₁⟩

end

/--
theorem `liftPropWithinAt_mono_of_mem_nhdsWithin` / 定理 `liftPropWithinAt_mono_of_mem_nhdsWithin`

English:
theorem liftPropWithinAt_mono_of_mem_nhdsWithin
  proof: by
  simp only [liftPropWithinAt_iff'] at h ⊢
  refine ⟨h.1.mono_of_mem_nhdsWithin hst, mono_of_mem_nhdsWithin ?_ h.2⟩
  simp_rw [← mem_map, (chartAt H x).symm.map_nhdsWithin_preimage_eq (mem_chart_target H x),
    (chartAt H x).left_inv (mem_chart_source H x), hst]

中文:
定理 liftPropWithinAt_mono_of_mem_nhdsWithin
  证明: by
  simp only [liftPropWithinAt_iff'] at h ⊢
  refine ⟨h.1.mono_of_mem_nhdsWithin hst, mono_of_mem_nhdsWithin ?_ h.2⟩
  simp_rw [← mem_map, (chartAt H x).symm.map_nhdsWithin_preimage_eq (mem_chart_target H x),
    (chartAt H x).left_inv (mem_chart_source H x), hst]

Depends on / 依赖: chartAt, left_inv, liftPropWithinAt_iff, map_nhdsWithin_preimage_eq, mem_chart_source, mem_chart_target, mem_map, mono_of_mem_nhdsWithin, simp_rw, symm.map_nhdsWithin_preimage_eq
-/
theorem liftPropWithinAt_mono_of_mem_nhdsWithin
    (mono_of_mem_nhdsWithin : forall ⦃s x t⦄ ⦃f : H -> H'⦄, s in 𝓝[t] x -> P f s x -> P f t x)
    (h : LiftPropWithinAt P g s x) (hst : s in 𝓝[t] x) : LiftPropWithinAt P g t x := by
  simp only [liftPropWithinAt_iff'] at h ⊢
  refine ⟨h.1.mono_of_mem_nhdsWithin hst, mono_of_mem_nhdsWithin ?_ h.2⟩
  simp_rw [← mem_map, (chartAt H x).symm.map_nhdsWithin_preimage_eq (mem_chart_target H x),
    (chartAt H x).left_inv (mem_chart_source H x), hst]

/--
theorem `liftPropWithinAt_mono` / 定理 `liftPropWithinAt_mono`

English:
theorem liftPropWithinAt_mono
  statement: (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x)
  proof: by
  refine ⟨h.1.mono hts, mono (fun y hy => ?_) h.2⟩
  simp only [mfld_simps] at hy
  simp only [hy, hts _, mfld_simps]

中文:
定理 liftPropWithinAt_mono
  结论: (mono : 对任意 ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x)
  证明: by
  refine ⟨h.1.mono hts, mono (fun y hy => ?_) h.2⟩
  simp only [mfld_simps] at hy
  simp only [hy, hts _, mfld_simps]

Depends on / 依赖: mfld_simps
-/
theorem liftPropWithinAt_mono (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x)
    (h : LiftPropWithinAt P g s x) (hts : t subseteq s) : LiftPropWithinAt P g t x := by
  refine ⟨h.1.mono hts, mono (fun y hy => ?_) h.2⟩
  simp only [mfld_simps] at hy
  simp only [hy, hts _, mfld_simps]

/--
theorem `liftPropWithinAt_of_liftPropAt` / 定理 `liftPropWithinAt_of_liftPropAt`

English:
theorem liftPropWithinAt_of_liftPropAt
  statement: (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x)
  proof: by
  rw [← liftPropWithinAt_univ] at h
  exact liftPropWithinAt_mono mono h (subset_univ _)

中文:
定理 liftPropWithinAt_of_liftPropAt
  结论: (mono : 对任意 ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x)
  证明: by
  rw [← liftPropWithinAt_univ] at h
  exact liftPropWithinAt_mono mono h (subset_univ _)

Depends on / 依赖: liftPropWithinAt_mono, liftPropWithinAt_univ, subset_univ
-/
theorem liftPropWithinAt_of_liftPropAt (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x)
    (h : LiftPropAt P g x) : LiftPropWithinAt P g s x := by
  rw [← liftPropWithinAt_univ] at h
  exact liftPropWithinAt_mono mono h (subset_univ _)

/--
theorem `liftPropOn_mono` / 定理 `liftPropOn_mono`

English:
theorem liftPropOn_mono
  statement: (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x)
  proof: fun x hx => liftPropWithinAt_mono mono (h x (hst hx)) hst

中文:
定理 liftPropOn_mono
  结论: (mono : 对任意 ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x)
  证明: fun x hx => liftPropWithinAt_mono mono (h x (hst hx)) hst

Depends on / 依赖: liftPropWithinAt_mono
-/
theorem liftPropOn_mono (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x)
    (h : LiftPropOn P g t) (hst : s subseteq t) : LiftPropOn P g s :=
  fun x hx => liftPropWithinAt_mono mono (h x (hst hx)) hst

/--
theorem `liftPropOn_of_liftProp` / 定理 `liftPropOn_of_liftProp`

English:
theorem liftPropOn_of_liftProp
  statement: (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x)
  proof: by
  rw [← liftPropOn_univ] at h
  exact liftPropOn_mono mono h (subset_univ _)

中文:
定理 liftPropOn_of_liftProp
  结论: (mono : 对任意 ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x)
  证明: by
  rw [← liftPropOn_univ] at h
  exact liftPropOn_mono mono h (subset_univ _)

Depends on / 依赖: liftPropOn_mono, liftPropOn_univ, subset_univ
-/
theorem liftPropOn_of_liftProp (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x)
    (h : LiftProp P g) : LiftPropOn P g s := by
  rw [← liftPropOn_univ] at h
  exact liftPropOn_mono mono h (subset_univ _)

/--
theorem `liftPropAt_of_mem_maximalAtlas` / 定理 `liftPropAt_of_mem_maximalAtlas`

English:
theorem liftPropAt_of_mem_maximalAtlas
  statement: (hG : G.LocalInvariantProp G Q)
  proof: by
  simp_rw [LiftPropAt, hG.liftPropWithinAt_indep_chart he hx G.id_mem_maximalAtlas (mem_univ _),
    (e.continuousAt hx).continuousWithinAt, true_and]
  exact hG.congr' (e.eventually_right_inverse' hx) (hQ _)

中文:
定理 liftPropAt_of_mem_maximalAtlas
  结论: (hG : G.LocalInvariant命题 G Q)
  证明: by
  simp_rw [LiftPropAt, hG.liftPropWithinAt_indep_chart he hx G.id_mem_maximalAtlas (mem_univ _),
    (e.continuousAt hx).continuousWithinAt, true_and]
  exact hG.congr' (e.eventually_right_inverse' hx) (hQ _)

Depends on / 依赖: G.id_mem_maximalAtlas, LiftPropAt, continuousAt, continuousWithinAt, e.continuousAt, e.eventually_right_inverse, eventually_right_inverse, hG.congr, hG.liftPropWithinAt_indep_chart, id_mem_maximalAtlas, liftPropWithinAt_indep_chart, mem_univ, simp_rw, true_and
-/
theorem liftPropAt_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q)
    (hQ : forall y, Q id univ y) (he : e in maximalAtlas M G) (hx : x in e.source) : LiftPropAt Q e x := by
  simp_rw [LiftPropAt, hG.liftPropWithinAt_indep_chart he hx G.id_mem_maximalAtlas (mem_univ _),
    (e.continuousAt hx).continuousWithinAt, true_and]
  exact hG.congr' (e.eventually_right_inverse' hx) (hQ _)

/--
theorem `liftPropOn_of_mem_maximalAtlas` / 定理 `liftPropOn_of_mem_maximalAtlas`

English:
theorem liftPropOn_of_mem_maximalAtlas
  statement: (hG : G.LocalInvariantProp G Q)
  proof: by
  intro x hx
  apply hG.liftPropWithinAt_of_liftPropAt_of_mem_nhds (hG.liftPropAt_of_mem_maximalAtlas hQ he hx)
  exact e.open_source.mem_nhds hx

中文:
定理 liftPropOn_of_mem_maximalAtlas
  结论: (hG : G.LocalInvariant命题 G Q)
  证明: by
  intro x hx
  apply hG.liftPropWithinAt_of_liftPropAt_of_mem_nhds (hG.liftPropAt_of_mem_maximalAtlas hQ he hx)
  exact e.open_source.mem_nhds hx

Depends on / 依赖: e.open_source.mem_nhds, hG.liftPropAt_of_mem_maximalAtlas, hG.liftPropWithinAt_of_liftPropAt_of_mem_nhds, liftPropAt_of_mem_maximalAtlas, liftPropWithinAt_of_liftPropAt_of_mem_nhds, mem_nhds, open_source
-/
theorem liftPropOn_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q)
    (hQ : forall y, Q id univ y) (he : e in maximalAtlas M G) : LiftPropOn Q e e.source := by
  intro x hx
  apply hG.liftPropWithinAt_of_liftPropAt_of_mem_nhds (hG.liftPropAt_of_mem_maximalAtlas hQ he hx)
  exact e.open_source.mem_nhds hx

/--
theorem `liftPropAt_symm_of_mem_maximalAtlas` / 定理 `liftPropAt_symm_of_mem_maximalAtlas`

English:
theorem liftPropAt_symm_of_mem_maximalAtlas
  statement: {x : H}
  proof: by
  suffices h : Q (e ∘ e.symm) univ x by
    have : e.symm x in e.source := by simp only [hx, mfld_simps]
    rw [LiftPropAt]; rw [hG.liftPropWithinAt_indep_chart G.id_mem_maximalAtlas (mem_univ _) he this]
    refine ⟨(e.symm.continuousAt hx).continuousWithinAt, ?_⟩
    simp only [h, mfld_simps]


中文:
定理 liftPropAt_symm_of_mem_maximalAtlas
  结论: {x : H}
  证明: by
  suffices h : Q (e ∘ e.symm) univ x by
    have : e.symm x in e.source := by simp only [hx, mfld_simps]
    rw [LiftPropAt]; rw [hG.liftPropWithinAt_indep_chart G.id_mem_maximalAtlas (mem_univ _) he this]
    refine ⟨(e.symm.continuousAt hx).continuousWithinAt, ?_⟩
    simp only [h, mfld_simps]


Depends on / 依赖: G.id_mem_maximalAtlas, LiftPropAt, continuousAt, continuousWithinAt, e.eventually_right_inverse, e.source, e.symm, e.symm.continuousAt, eventually_right_inverse, hG.congr, hG.liftPropWithinAt_indep_chart, id_mem_maximalAtlas, liftPropWithinAt_indep_chart, mem_univ, mfld_simps, source
-/
theorem liftPropAt_symm_of_mem_maximalAtlas {x : H}
    (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id univ y) (he : e in maximalAtlas M G)
    (hx : x in e.target) : LiftPropAt Q e.symm x := by
  suffices h : Q (e ∘ e.symm) univ x by
    have : e.symm x in e.source := by simp only [hx, mfld_simps]
    rw [LiftPropAt]; rw [hG.liftPropWithinAt_indep_chart G.id_mem_maximalAtlas (mem_univ _) he this]
    refine ⟨(e.symm.continuousAt hx).continuousWithinAt, ?_⟩
    simp only [h, mfld_simps]
  exact hG.congr' (e.eventually_right_inverse hx) (hQ x)

/--
theorem `liftPropOn_symm_of_mem_maximalAtlas` / 定理 `liftPropOn_symm_of_mem_maximalAtlas`

English:
theorem liftPropOn_symm_of_mem_maximalAtlas
  statement: (hG : G.LocalInvariantProp G Q)
  proof: by
  intro x hx
  apply hG.liftPropWithinAt_of_liftPropAt_of_mem_nhds
    (hG.liftPropAt_symm_of_mem_maximalAtlas hQ he hx)
  exact e.open_target.mem_nhds hx

中文:
定理 liftPropOn_symm_of_mem_maximalAtlas
  结论: (hG : G.LocalInvariant命题 G Q)
  证明: by
  intro x hx
  apply hG.liftPropWithinAt_of_liftPropAt_of_mem_nhds
    (hG.liftPropAt_symm_of_mem_maximalAtlas hQ he hx)
  exact e.open_target.mem_nhds hx

Depends on / 依赖: e.open_target.mem_nhds, hG.liftPropAt_symm_of_mem_maximalAtlas, hG.liftPropWithinAt_of_liftPropAt_of_mem_nhds, liftPropAt_symm_of_mem_maximalAtlas, liftPropWithinAt_of_liftPropAt_of_mem_nhds, mem_nhds, open_target
-/
theorem liftPropOn_symm_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q)
    (hQ : forall y, Q id univ y) (he : e in maximalAtlas M G) : LiftPropOn Q e.symm e.target := by
  intro x hx
  apply hG.liftPropWithinAt_of_liftPropAt_of_mem_nhds
    (hG.liftPropAt_symm_of_mem_maximalAtlas hQ he hx)
  exact e.open_target.mem_nhds hx

/--
theorem `liftPropAt_chart` / 定理 `liftPropAt_chart`

English:
theorem liftPropAt_chart
  given: [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id univ y)
  proof: hG.liftPropAt_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x) (mem_chart_source H x)

中文:
定理 liftPropAt_chart
  条件: [HasGroupoid M G] (hG : G.LocalInvariant命题 G Q) (hQ : 对任意 y, Q id univ y)
  证明: hG.liftPropAt_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x) (mem_chart_source H x)
-/
theorem liftPropAt_chart [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id univ y) :
    LiftPropAt Q (chartAt (H := H) x) x :=
  hG.liftPropAt_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x) (mem_chart_source H x)

/--
theorem `liftPropOn_chart` / 定理 `liftPropOn_chart`

English:
theorem liftPropOn_chart
  given: [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id univ y)
  proof: hG.liftPropOn_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x)

中文:
定理 liftPropOn_chart
  条件: [HasGroupoid M G] (hG : G.LocalInvariant命题 G Q) (hQ : 对任意 y, Q id univ y)
  证明: hG.liftPropOn_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x)

Depends on / 依赖: chartAt, source
-/
theorem liftPropOn_chart [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id univ y) :
    LiftPropOn Q (chartAt (H := H) x) (chartAt (H := H) x).source :=
  hG.liftPropOn_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x)

/--
theorem `liftPropAt_chart_symm` / 定理 `liftPropAt_chart_symm`

English:
theorem liftPropAt_chart_symm
  statement: [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
  proof: hG.liftPropAt_symm_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x) (by simp)

中文:
定理 liftPropAt_chart_symm
  结论: [HasGroupoid M G] (hG : G.LocalInvariant命题 G Q)
  证明: hG.liftPropAt_symm_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x) (by simp)

Depends on / 依赖: chartAt
-/
theorem liftPropAt_chart_symm [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : forall y, Q id univ y) : LiftPropAt Q (chartAt (H := H) x).symm ((chartAt H x) x) :=
  hG.liftPropAt_symm_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x) (by simp)

/--
theorem `liftPropOn_chart_symm` / 定理 `liftPropOn_chart_symm`

English:
theorem liftPropOn_chart_symm
  statement: [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
  proof: hG.liftPropOn_symm_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x)

中文:
定理 liftPropOn_chart_symm
  结论: [HasGroupoid M G] (hG : G.LocalInvariant命题 G Q)
  证明: hG.liftPropOn_symm_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x)

Depends on / 依赖: chartAt, target
-/
theorem liftPropOn_chart_symm [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : forall y, Q id univ y) : LiftPropOn Q (chartAt (H := H) x).symm (chartAt H x).target :=
  hG.liftPropOn_symm_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x)

/--
theorem `liftPropAt_of_mem_groupoid` / 定理 `liftPropAt_of_mem_groupoid`

English:
theorem liftPropAt_of_mem_groupoid
  statement: (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id univ y)
  proof: liftPropAt_of_mem_maximalAtlas hG hQ (G.mem_maximalAtlas_of_mem_groupoid hf) hx

中文:
定理 liftPropAt_of_mem_groupoid
  结论: (hG : G.LocalInvariant命题 G Q) (hQ : 对任意 y, Q id univ y)
  证明: liftPropAt_of_mem_maximalAtlas hG hQ (G.mem_maximalAtlas_of_mem_groupoid hf) hx

Depends on / 依赖: G.mem_maximalAtlas_of_mem_groupoid, liftPropAt_of_mem_maximalAtlas, mem_maximalAtlas_of_mem_groupoid
-/
theorem liftPropAt_of_mem_groupoid (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id univ y)
    {f : OpenPartialHomeomorph H H} (hf : f in G) {x : H} (hx : x in f.source) : LiftPropAt Q f x :=
  liftPropAt_of_mem_maximalAtlas hG hQ (G.mem_maximalAtlas_of_mem_groupoid hf) hx

/--
theorem `liftPropOn_of_mem_groupoid` / 定理 `liftPropOn_of_mem_groupoid`

English:
theorem liftPropOn_of_mem_groupoid
  statement: (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id univ y)
  proof: liftPropOn_of_mem_maximalAtlas hG hQ (G.mem_maximalAtlas_of_mem_groupoid hf)

中文:
定理 liftPropOn_of_mem_groupoid
  结论: (hG : G.LocalInvariant命题 G Q) (hQ : 对任意 y, Q id univ y)
  证明: liftPropOn_of_mem_maximalAtlas hG hQ (G.mem_maximalAtlas_of_mem_groupoid hf)

Depends on / 依赖: G.mem_maximalAtlas_of_mem_groupoid, liftPropOn_of_mem_maximalAtlas, mem_maximalAtlas_of_mem_groupoid
-/
theorem liftPropOn_of_mem_groupoid (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id univ y)
    {f : OpenPartialHomeomorph H H} (hf : f in G) : LiftPropOn Q f f.source :=
  liftPropOn_of_mem_maximalAtlas hG hQ (G.mem_maximalAtlas_of_mem_groupoid hf)

/--
theorem `liftProp_id` / 定理 `liftProp_id`

English:
theorem liftProp_id
  given: (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id univ y)
  proof: by
  simp_rw [liftProp_iff, continuous_id, true_and]
  exact fun x => hG.congr' ((chartAt H x).eventually_right_inverse <| mem_chart_target H x) (hQ _)

中文:
定理 liftProp_id
  条件: (hG : G.LocalInvariant命题 G Q) (hQ : 对任意 y, Q id univ y)
  证明: by
  simp_rw [liftProp_iff, continuous_id, true_and]
  exact fun x => hG.congr' ((chartAt H x).eventually_right_inverse <| mem_chart_target H x) (hQ _)

Depends on / 依赖: chartAt, continuous_id, eventually_right_inverse, hG.congr, liftProp_iff, mem_chart_target, simp_rw, true_and
-/
theorem liftProp_id (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id univ y) :
    LiftProp Q (id : M -> M) := by
  simp_rw [liftProp_iff, continuous_id, true_and]
  exact fun x => hG.congr' ((chartAt H x).eventually_right_inverse <| mem_chart_target H x) (hQ _)

/--
theorem `liftPropAt_iff_comp_subtype_val` / 定理 `liftPropAt_iff_comp_subtype_val`

English:
theorem liftPropAt_iff_comp_subtype_val
  statement: (hG : LocalInvariantProp G G' P) {U : Opens M}
  proof: by
  simp only [LiftPropAt, liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · simp_rw [continuousWithinAt_univ, U.isOpenEmbedding'.continuousAt_iff]
  · apply hG.congr_iff
    exact (U.chartAt_subtype_val_symm_eventuallyEq).fun_comp (chartAt H' (f x) ∘ f)

中文:
定理 liftPropAt_iff_comp_subtype_val
  结论: (hG : LocalInvariant命题 G G' P) {U : Opens M}
  证明: by
  simp only [LiftPropAt, liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · simp_rw [continuousWithinAt_univ, U.isOpenEmbedding'.continuousAt_iff]
  · apply hG.congr_iff
    exact (U.chartAt_subtype_val_symm_eventuallyEq).fun_comp (chartAt H' (f x) ∘ f)

Depends on / 依赖: LiftPropAt, U.chartAt_subtype_val_symm_eventuallyEq, U.isOpenEmbedding, chartAt, chartAt_subtype_val_symm_eventuallyEq, congr_iff, congrm, continuousAt_iff, continuousWithinAt_univ, fun_comp, hG.congr_iff, isOpenEmbedding, liftPropWithinAt_iff, simp_rw
-/
theorem liftPropAt_iff_comp_subtype_val (hG : LocalInvariantProp G G' P) {U : Opens M}
    (f : M -> M') (x : U) :
    LiftPropAt P f x ↔ LiftPropAt P (f ∘ Subtype.val) x := by
  simp only [LiftPropAt, liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · simp_rw [continuousWithinAt_univ, U.isOpenEmbedding'.continuousAt_iff]
  · apply hG.congr_iff
    exact (U.chartAt_subtype_val_symm_eventuallyEq).fun_comp (chartAt H' (f x) ∘ f)

/--
theorem `liftPropAt_iff_comp_inclusion` / 定理 `liftPropAt_iff_comp_inclusion`

English:
theorem liftPropAt_iff_comp_inclusion
  statement: (hG : LocalInvariantProp G G' P) {U V : Opens M} (hUV : U <= V)
  proof: by
  simp only [LiftPropAt, liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · simp_rw [continuousWithinAt_univ,
      (TopologicalSpace.Opens.isOpenEmbedding_of_le hUV).continuousAt_iff]
  · apply hG.congr_iff
    exact (TopologicalSpace.Opens.chartAt_inclusion_symm_eventuallyEq hUV).fun_comp
      (chart

中文:
定理 liftPropAt_iff_comp_inclusion
  结论: (hG : LocalInvariant命题 G G' P) {U V : Opens M} (hUV : U <= V)
  证明: by
  simp only [LiftPropAt, liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · simp_rw [continuousWithinAt_univ,
      (TopologicalSpace.Opens.isOpenEmbedding_of_le hUV).continuousAt_iff]
  · apply hG.congr_iff
    exact (TopologicalSpace.Opens.chartAt_inclusion_symm_eventuallyEq hUV).fun_comp
      (chart

Depends on / 依赖: LiftPropAt, Set.inclusion, TopologicalSpace, TopologicalSpace.Opens.chartAt_inclusion_symm_eventuallyEq, TopologicalSpace.Opens.isOpenEmbedding_of_le, chartAt, chartAt_inclusion_symm_eventuallyEq, congr_iff, congrm, continuousAt_iff, continuousWithinAt_univ, fun_comp, hG.congr_iff, inclusion, isOpenEmbedding_of_le, liftPropWithinAt_iff, simp_rw
-/
theorem liftPropAt_iff_comp_inclusion (hG : LocalInvariantProp G G' P) {U V : Opens M} (hUV : U <= V)
    (f : V -> M') (x : U) :
    LiftPropAt P f (Set.inclusion hUV x) ↔ LiftPropAt P (f ∘ Set.inclusion hUV : U -> M') x := by
  simp only [LiftPropAt, liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · simp_rw [continuousWithinAt_univ,
      (TopologicalSpace.Opens.isOpenEmbedding_of_le hUV).continuousAt_iff]
  · apply hG.congr_iff
    exact (TopologicalSpace.Opens.chartAt_inclusion_symm_eventuallyEq hUV).fun_comp
      (chartAt H' (f (Set.inclusion hUV x)) ∘ f)

/--
theorem `liftProp_subtype_val` / 定理 `liftProp_subtype_val`

English:
theorem liftProp_subtype_val
  statement: {Q : (H -> H) -> Set H -> H -> Prop} (hG : LocalInvariantProp G G Q)
  proof: by
  intro x
  change LiftPropAt Q (id ∘ Subtype.val) x
  rw [← hG.liftPropAt_iff_comp_subtype_val]
  apply hG.liftProp_id hQ

中文:
定理 liftProp_subtype_val
  结论: {Q : (H -> H) -> Set H -> H -> 命题} (hG : LocalInvariant命题 G G Q)
  证明: by
  intro x
  change LiftPropAt Q (id ∘ Subtype.val) x
  rw [← hG.liftPropAt_iff_comp_subtype_val]
  apply hG.liftProp_id hQ

Depends on / 依赖: LiftPropAt, Subtype, Subtype.val, hG.liftPropAt_iff_comp_subtype_val, hG.liftProp_id, liftPropAt_iff_comp_subtype_val, liftProp_id
-/
theorem liftProp_subtype_val {Q : (H -> H) -> Set H -> H -> Prop} (hG : LocalInvariantProp G G Q)
    (hQ : forall y, Q id univ y) (U : Opens M) :
    LiftProp Q (Subtype.val : U -> M) := by
  intro x
  change LiftPropAt Q (id ∘ Subtype.val) x
  rw [← hG.liftPropAt_iff_comp_subtype_val]
  apply hG.liftProp_id hQ

/--
theorem `liftProp_inclusion` / 定理 `liftProp_inclusion`

English:
theorem liftProp_inclusion
  statement: {Q : (H -> H) -> Set H -> H -> Prop} (hG : LocalInvariantProp G G Q)
  proof: by
  intro x
  change LiftPropAt Q (id ∘ Opens.inclusion hUV) x
  rw [← hG.liftPropAt_iff_comp_inclusion hUV]
  apply hG.liftProp_id hQ

中文:
定理 liftProp_inclusion
  结论: {Q : (H -> H) -> Set H -> H -> 命题} (hG : LocalInvariant命题 G G Q)
  证明: by
  intro x
  change LiftPropAt Q (id ∘ Opens.inclusion hUV) x
  rw [← hG.liftPropAt_iff_comp_inclusion hUV]
  apply hG.liftProp_id hQ

Depends on / 依赖: LiftPropAt, Opens.inclusion, hG.liftPropAt_iff_comp_inclusion, hG.liftProp_id, inclusion, liftPropAt_iff_comp_inclusion, liftProp_id
-/
theorem liftProp_inclusion {Q : (H -> H) -> Set H -> H -> Prop} (hG : LocalInvariantProp G G Q)
    (hQ : forall y, Q id univ y) {U V : Opens M} (hUV : U <= V) :
    LiftProp Q (Opens.inclusion hUV : U -> V) := by
  intro x
  change LiftPropAt Q (id ∘ Opens.inclusion hUV) x
  rw [← hG.liftPropAt_iff_comp_inclusion hUV]
  apply hG.liftProp_id hQ

end LocalInvariantProp

section LocalStructomorph

variable (G)

open OpenPartialHomeomorph

/--
Definition of `IsLocalStructomorphWithinAt` / `IsLocalStructomorphWithinAt` 的定义

English:
definition IsLocalStructomorphWithinAt
  signature: (f : H -> H) (s : Set H) (x : H)
  body: x in s -> exists e : OpenPartialHomeomorph H H, e in G ∧ EqOn f e.toFun (s inter e.source) ∧ x in e.source

中文:
定义 IsLocalStructomorphWithinAt
  签名: (f : H -> H) (s : Set H) (x : H)
  定义体: x in s -> exists e : OpenPartialHomeomorph H H, e in G ∧ EqOn f e.toFun (s inter e.source) ∧ x in e.source

Depends on / 依赖: OpenPartialHomeomorph, e.source, e.toFun, source
-/
def IsLocalStructomorphWithinAt (f : H -> H) (s : Set H) (x : H) : Prop :=
  x in s -> exists e : OpenPartialHomeomorph H H, e in G ∧ EqOn f e.toFun (s inter e.source) ∧ x in e.source

/--
theorem `isLocalStructomorphWithinAt_localInvariantProp` / 定理 `isLocalStructomorphWithinAt_localInvariantProp`

English:
theorem isLocalStructomorphWithinAt_localInvariantProp
  given: [ClosedUnderRestriction G]
  proof: { is_local := by
      intro s x u f hu hux
      constructor
      · rintro h hx
        rcases h hx.1 with ⟨e, heG, hef, hex⟩
        have : s inter u inter e.source subseteq s inter e.source := by mfld_set_tac
        exact ⟨e, heG, hef.mono this, hex⟩
      · rintro h hx
        rcases h ⟨hx, hu

中文:
定理 isLocalStructomorphWithinAt_localInvariantProp
  条件: [ClosedUnderRestriction G]
  证明: { is_local := by
      intro s x u f hu hux
      constructor
      · rintro h hx
        rcases h hx.1 with ⟨e, heG, hef, hex⟩
        have : s inter u inter e.source subseteq s inter e.source := by mfld_set_tac
        exact ⟨e, heG, hef.mono this, hex⟩
      · rintro h hx
        rcases h ⟨hx, hu

Depends on / 依赖: closedUnderRestriction, e.restr, e.source, hef.mono, hu.interior_eq, interior, interior_eq, interior_interior, isOpen_interior, is_local, mfld_set_tac, source, subseteq
-/
theorem isLocalStructomorphWithinAt_localInvariantProp [ClosedUnderRestriction G] :
    LocalInvariantProp G G (IsLocalStructomorphWithinAt G) :=
  { is_local := by
      intro s x u f hu hux
      constructor
      · rintro h hx
        rcases h hx.1 with ⟨e, heG, hef, hex⟩
        have : s inter u inter e.source subseteq s inter e.source := by mfld_set_tac
        exact ⟨e, heG, hef.mono this, hex⟩
      · rintro h hx
        rcases h ⟨hx, hux⟩ with ⟨e, heG, hef, hex⟩
        refine ⟨e.restr (interior u), ?_, ?_, ?_⟩
        · exact closedUnderRestriction' heG isOpen_interior
        · have : s inter u inter e.source = s inter (e.source inter u) := by mfld_set_tac
          simpa only [this, interior_interior, hu.interior_eq, mfld_simps] using hef
        · simp only [*, hu.interior_eq, mfld_simps]
    right_invariance' := by
      intro s x f e' he'G he'x h hx
      have hxs : x in s := by simpa only [e'.left_inv he'x, mfld_simps] using hx
      rcases h hxs with ⟨e, heG, hef, hex⟩
      refine ⟨e'.symm.trans e, G.trans (G.symm he'G) heG, ?_, ?_⟩
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [hef ⟨hy.1, hy.2.2⟩, mfld_simps]
      · simp only [hex, he'x, mfld_simps]
    congr_of_forall := by
      intro s x f g hfgs _ h hx
      rcases h hx with ⟨e, heG, hef, hex⟩
      refine ⟨e, heG, ?_, hex⟩
      intro y hy
      rw [← hef hy]; rw [hfgs y hy.1]
    left_invariance' := by
      intro s x f e' he'G _ hfx h hx
      rcases h hx with ⟨e, heG, hef, hex⟩
      refine ⟨e.trans e', G.trans heG he'G, ?_, ?_⟩
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [hef ⟨hy.1, hy.2.1⟩, mfld_simps]
      · simpa only [hex, hef ⟨hx, hex⟩, mfld_simps] using hfx }

/--
theorem `_root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff` / 定理 `_root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff`

English:
theorem _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff
  statement: {G : StructureGroupoid H}
  proof: by
  constructor
  · intro hf h2x
    obtain ⟨e, he, hfe, hxe⟩ := hf h2x
    refine ⟨e.restr f.source, closedUnderRestriction' he f.open_source, ?_, ?_, hxe, ?_⟩
    · simp_rw [OpenPartialHomeomorph.restr_source]
      exact inter_subset_right.trans interior_subset
    · intro x' hx'
      exact hfe

中文:
定理 _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff
  结论: {G : StructureGroupoid H}
  证明: by
  constructor
  · intro hf h2x
    obtain ⟨e, he, hfe, hxe⟩ := hf h2x
    refine ⟨e.restr f.source, closedUnderRestriction' he f.open_source, ?_, ?_, hxe, ?_⟩
    · simp_rw [OpenPartialHomeomorph.restr_source]
      exact inter_subset_right.trans interior_subset
    · intro x' hx'
      exact hfe

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.restr_source, Or.resolve_right, closedUnderRestriction, e.restr, f.open_source, f.open_source.interior_eq, f.source, inter_subset_right, inter_subset_right.trans, interior_eq, interior_subset, not_not, not_not.mpr, open_source, resolve_right, restr_source, simp_rw, source
-/
theorem _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff {G : StructureGroupoid H}
    [ClosedUnderRestriction G] (f : OpenPartialHomeomorph H H) {s : Set H} {x : H}
    (hx : x in f.source union sᶜ) :
    G.IsLocalStructomorphWithinAt (⇑f) s x ↔
      x in s -> exists e : OpenPartialHomeomorph H H,
      e in G ∧ e.source subseteq f.source ∧ EqOn f (⇑e) (s inter e.source) ∧ x in e.source := by
  constructor
  · intro hf h2x
    obtain ⟨e, he, hfe, hxe⟩ := hf h2x
    refine ⟨e.restr f.source, closedUnderRestriction' he f.open_source, ?_, ?_, hxe, ?_⟩
    · simp_rw [OpenPartialHomeomorph.restr_source]
      exact inter_subset_right.trans interior_subset
    · intro x' hx'
      exact hfe ⟨hx'.1, hx'.2.1⟩
    · rw [f.open_source.interior_eq]
      exact Or.resolve_right hx (not_not.mpr h2x)
  · intro hf hx
    obtain ⟨e, he, _, hfe, hxe⟩ := hf hx
    exact ⟨e, he, hfe, hxe⟩

/--
theorem `_root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff'` / 定理 `_root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff'`

English:
theorem _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff'
  statement: {G : StructureGroupoid H}
  proof: by
  rw [f.isLocalStructomorphWithinAt_iff hx]
  refine imp_congr_right fun _ => exists_congr fun e => and_congr_right fun _ => ?_
  refine and_congr_right fun h2e => ?_
  rw [inter_eq_right.mpr (h2e.trans hs)]

中文:
定理 _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff'
  结论: {G : StructureGroupoid H}
  证明: by
  rw [f.isLocalStructomorphWithinAt_iff hx]
  refine imp_congr_right fun _ => exists_congr fun e => and_congr_right fun _ => ?_
  refine and_congr_right fun h2e => ?_
  rw [inter_eq_right.mpr (h2e.trans hs)]

Depends on / 依赖: and_congr_right, exists_congr, f.isLocalStructomorphWithinAt_iff, h2e.trans, imp_congr_right, inter_eq_right, inter_eq_right.mpr, isLocalStructomorphWithinAt_iff
-/
theorem _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff' {G : StructureGroupoid H}
    [ClosedUnderRestriction G] (f : OpenPartialHomeomorph H H) {s : Set H} {x : H}
    (hs : f.source subseteq s) (hx : x in f.source union sᶜ) :
    G.IsLocalStructomorphWithinAt (⇑f) s x ↔
      x in s -> exists e : OpenPartialHomeomorph H H,
      e in G ∧ e.source subseteq f.source ∧ EqOn f (⇑e) e.source ∧ x in e.source := by
  rw [f.isLocalStructomorphWithinAt_iff hx]
  refine imp_congr_right fun _ => exists_congr fun e => and_congr_right fun _ => ?_
  refine and_congr_right fun h2e => ?_
  rw [inter_eq_right.mpr (h2e.trans hs)]

/--
theorem `_root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff` / 定理 `_root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff`

English:
theorem _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff
  proof: haveI : x in f.source union f.sourceᶜ := by simp_rw [union_compl_self, mem_univ]
  f.isLocalStructomorphWithinAt_iff' Subset.rfl this

中文:
定理 _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff
  证明: haveI : x in f.source union f.sourceᶜ := by simp_rw [union_compl_self, mem_univ]
  f.isLocalStructomorphWithinAt_iff' Subset.rfl this

Depends on / 依赖: Subset, Subset.rfl, f.isLocalStructomorphWithinAt_iff, f.source, isLocalStructomorphWithinAt_iff, mem_univ, simp_rw, source, union_compl_self
-/
theorem _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff
    {G : StructureGroupoid H} [ClosedUnderRestriction G] (f : OpenPartialHomeomorph H H) {x : H} :
    G.IsLocalStructomorphWithinAt (⇑f) f.source x ↔
      x in f.source -> exists e : OpenPartialHomeomorph H H,
      e in G ∧ e.source subseteq f.source ∧ EqOn f (⇑e) e.source ∧ x in e.source :=
  haveI : x in f.source union f.sourceᶜ := by simp_rw [union_compl_self, mem_univ]
  f.isLocalStructomorphWithinAt_iff' Subset.rfl this

variable {H₁ : Type*} [TopologicalSpace H₁] {H₂ : Type*} [TopologicalSpace H₂] {H₃ : Type*}
  [TopologicalSpace H₃] [ChartedSpace H₁ H₂] [ChartedSpace H₂ H₃] {G₁ : StructureGroupoid H₁}
  [HasGroupoid H₂ G₁] [ClosedUnderRestriction G₁] (G₂ : StructureGroupoid H₂) [HasGroupoid H₃ G₂]

/--
theorem `HasGroupoid.comp` / 定理 `HasGroupoid.comp`

English:
theorem HasGroupoid.comp
  proof: let _ := ChartedSpace.comp H₁ H₂ H₃
  { compatible := by
      rintro _ _ ⟨e, he, f, hf, rfl⟩ ⟨e', he', f', hf', rfl⟩
      apply G₁.locality
      intro x hx
      simp only [mfld_simps] at hx
      have hxs : x in f.symm ⁻¹' (e.symm ≫ₕ e').source := by simp only [hx, mfld_simps]
      have hxs' : 

中文:
定理 HasGroupoid.comp
  证明: let _ := ChartedSpace.comp H₁ H₂ H₃
  { compatible := by
      rintro _ _ ⟨e, he, f, hf, rfl⟩ ⟨e', he', f', hf', rfl⟩
      apply G₁.locality
      intro x hx
      simp only [mfld_simps] at hx
      have hxs : x in f.symm ⁻¹' (e.symm ≫ₕ e').source := by simp only [hx, mfld_simps]
      have hxs' : 

Depends on / 依赖: ChartedSpace, ChartedSpace.comp, LocalInvariantProp, LocalInvariantProp.liftPropOn_indep_chart, compatible, e.symm, f.symm, f.target, isLocalStructomorphWithinAt_localInvariant, liftPropOn_indep_chart, locality, mfld_simps, source, target
-/
theorem HasGroupoid.comp
    (H : forall e in G₂, LiftPropOn (IsLocalStructomorphWithinAt G₁) (e : H₂ -> H₂) e.source) :
    @HasGroupoid H₁ _ H₃ _ (ChartedSpace.comp H₁ H₂ H₃) G₁ :=
  let _ := ChartedSpace.comp H₁ H₂ H₃
  { compatible := by
      rintro _ _ ⟨e, he, f, hf, rfl⟩ ⟨e', he', f', hf', rfl⟩
      apply G₁.locality
      intro x hx
      simp only [mfld_simps] at hx
      have hxs : x in f.symm ⁻¹' (e.symm ≫ₕ e').source := by simp only [hx, mfld_simps]
      have hxs' : x in f.target inter
          f.symm ⁻¹' ((e.symm ≫ₕ e').source inter e.symm ≫ₕ e' ⁻¹' f'.source) := by
        simp only [hx, mfld_simps]
      obtain ⟨φ, hφG₁, hφ, hφ_dom⟩ := LocalInvariantProp.liftPropOn_indep_chart
        (isLocalStructomorphWithinAt_localInvariantProp G₁) (G₁.subset_maximalAtlas hf)
        (G₁.subset_maximalAtlas hf') (H _ (G₂.compatible he he')) hxs' hxs
      simp_rw [← OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_assoc] at hφ
      simp_rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc]
      have hs : IsOpen (f.symm ≫ₕ e.symm ≫ₕ e' ≫ₕ f').source :=
        (f.symm ≫ₕ e.symm ≫ₕ e' ≫ₕ f').open_source
      refine ⟨_, hs.inter φ.open_source, ?_, ?_⟩
      · simp only [hx, hφ_dom, mfld_simps]
      · refine G₁.mem_of_eqOnSource (closedUnderRestriction' hφG₁ hs) ?_
        rw [OpenPartialHomeomorph.restr_source_inter]
        refine OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source (hφ.mono ?_)
        mfld_set_tac }

end LocalStructomorph

end StructureGroupoid
