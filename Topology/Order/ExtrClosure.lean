/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.LocalExtr

/-!
# Maximum/minimum on the closure of a set

In this file we prove several versions of the following statement: if `f : X → Y` has a (local or
not) maximum (or minimum) on a set `s` at a point `a` and is continuous on the closure of `s`, then
`f` has an extremum of the same type on `Closure s` at `a`.
-/

public section


open Filter Set

open Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Preorder Y]
  [OrderClosedTopology Y] {f : X -> Y} {s : Set X} {a : X}

/--
theorem `IsMaxOn.closure` / 定理 `IsMaxOn.closure`

English:
theorem IsMaxOn.closure
  given: (h : IsMaxOn f s a) (hc : ContinuousOn f (closure s))
  proof: fun x hx =>
  ContinuousWithinAt.closure_le hx ((hc x hx).mono subset_closure) continuousWithinAt_const h

中文:
定理 IsMaxOn.closure
  条件: (h : IsMaxOn f s a) (hc : ContinuousOn f (closure s))
  证明: fun x hx =>
  ContinuousWithinAt.closure_le hx ((hc x hx).mono subset_closure) continuousWithinAt_const h
-/
protected theorem IsMaxOn.closure (h : IsMaxOn f s a) (hc : ContinuousOn f (closure s)) :
    IsMaxOn f (closure s) a := fun x hx =>
  ContinuousWithinAt.closure_le hx ((hc x hx).mono subset_closure) continuousWithinAt_const h

/--
theorem `IsMinOn.closure` / 定理 `IsMinOn.closure`

English:
theorem IsMinOn.closure
  given: (h : IsMinOn f s a) (hc : ContinuousOn f (closure s))
  proof: h.dual.closure hc

中文:
定理 IsMinOn.closure
  条件: (h : IsMinOn f s a) (hc : ContinuousOn f (closure s))
  证明: h.dual.closure hc
-/
protected theorem IsMinOn.closure (h : IsMinOn f s a) (hc : ContinuousOn f (closure s)) :
    IsMinOn f (closure s) a :=
  h.dual.closure hc

/--
theorem `IsExtrOn.closure` / 定理 `IsExtrOn.closure`

English:
theorem IsExtrOn.closure
  given: (h : IsExtrOn f s a) (hc : ContinuousOn f (closure s))
  proof: h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr h.closure hc

中文:
定理 IsExtrOn.closure
  条件: (h : IsExtrOn f s a) (hc : ContinuousOn f (closure s))
  证明: h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr h.closure hc
-/
protected theorem IsExtrOn.closure (h : IsExtrOn f s a) (hc : ContinuousOn f (closure s)) :
    IsExtrOn f (closure s) a :=
h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr h.closure hc

/--
theorem `IsLocalMaxOn.closure` / 定理 `IsLocalMaxOn.closure`

English:
theorem IsLocalMaxOn.closure
  given: (h : IsLocalMaxOn f s a) (hc : ContinuousOn f (closure s))
  proof: by
  rcases mem_nhdsWithin.1 h with ⟨U, Uo, aU, hU⟩
  refine mem_nhdsWithin.2 ⟨U, Uo, aU, ?_⟩
  rintro x ⟨hxU, hxs⟩
  refine ContinuousWithinAt.closure_le ?_ ?_ continuousWithinAt_const hU
  · rwa [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_inter_of_mem, ←
      mem_closure_iff_nhdsWithin_neBot]
    exact nhdsWithin_le_nhds (Uo.mem_nhds hxU)
  · exact (hc _ hxs).mono (inter_subset_right.trans subset_closure)

中文:
定理 IsLocalMaxOn.closure
  条件: (h : IsLocalMaxOn f s a) (hc : ContinuousOn f (closure s))
  证明: by
  rcases mem_nhdsWithin.1 h with ⟨U, Uo, aU, hU⟩
  refine mem_nhdsWithin.2 ⟨U, Uo, aU, ?_⟩
  rintro x ⟨hxU, hxs⟩
  refine ContinuousWithinAt.closure_le ?_ ?_ continuousWithinAt_const hU
  · rwa [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_inter_of_mem, ←
      mem_closure_iff_nhdsWithin_neBot]
    exact nhdsWithin_le_nhds (Uo.mem_nhds hxU)
  · exact (hc _ hxs).mono (inter_subset_right.trans subset_closure)
-/
protected theorem IsLocalMaxOn.closure (h : IsLocalMaxOn f s a) (hc : ContinuousOn f (closure s)) :
    IsLocalMaxOn f (closure s) a := by
  rcases mem_nhdsWithin.1 h with ⟨U, Uo, aU, hU⟩
  refine mem_nhdsWithin.2 ⟨U, Uo, aU, ?_⟩
  rintro x ⟨hxU, hxs⟩
  refine ContinuousWithinAt.closure_le ?_ ?_ continuousWithinAt_const hU
  · rwa [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_inter_of_mem, ←
      mem_closure_iff_nhdsWithin_neBot]
    exact nhdsWithin_le_nhds (Uo.mem_nhds hxU)
  · exact (hc _ hxs).mono (inter_subset_right.trans subset_closure)

/--
theorem `IsLocalMinOn.closure` / 定理 `IsLocalMinOn.closure`

English:
theorem IsLocalMinOn.closure
  given: (h : IsLocalMinOn f s a) (hc : ContinuousOn f (closure s))
  proof: IsLocalMaxOn.closure h.dual hc

中文:
定理 IsLocalMinOn.closure
  条件: (h : IsLocalMinOn f s a) (hc : ContinuousOn f (closure s))
  证明: IsLocalMaxOn.closure h.dual hc
-/
protected theorem IsLocalMinOn.closure (h : IsLocalMinOn f s a) (hc : ContinuousOn f (closure s)) :
    IsLocalMinOn f (closure s) a :=
  IsLocalMaxOn.closure h.dual hc

/--
theorem `IsLocalExtrOn.closure` / 定理 `IsLocalExtrOn.closure`

English:
theorem IsLocalExtrOn.closure
  statement: (h : IsLocalExtrOn f s a)
  proof: h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr h.closure hc

中文:
定理 IsLocalExtrOn.closure
  结论: (h : IsLocalExtrOn f s a)
  证明: h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr h.closure hc
-/
protected theorem IsLocalExtrOn.closure (h : IsLocalExtrOn f s a)
    (hc : ContinuousOn f (closure s)) : IsLocalExtrOn f (closure s) a :=
h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr h.closure hc
