/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Idempotent continuous linear maps

In this file, we study the idempotent elements (`IsIdempotentElem`) of the ring `M →L[R] M` of
continuous endomorphisms of a topological `R`-module `M`.

## Main statements

* `ContinuousLinearMap.isIdempotentElem_toLinearMap_iff`: `T` is idempotent as an element of
  `M →L[R] M` if and only if it is such as an element of `M →ₗ[R] M`;
* `ContinuousLinearMap.IsIdempotentElem.ext_iff`: idempotent elements of `M →L[R] M` are determined
  by their range and kernel;
* `ContinuousLinearMap.IsIdempotentElem.commute_iff`: a continuous linear map `S` commutes with
  an idempotent `T` if and only if the range and kernel of `T` are `S`-invariant;
* `ContinuousLinearMap.IsIdempotentElem.isCLosed_range`: an idempotent continuous linear map
  has closed range.

Further results can be found in the `Mathlib/Topology/Algebra/Module/Complement.lean` module, where
we show that idempotent elements of `M →L[R] M` are precisely the projections associated to
topological complement submodules.
-/

@[expose] public section

namespace ContinuousLinearMap

@[grind =]
/--
theorem `isIdempotentElem_toLinearMap_iff` / 定理 `isIdempotentElem_toLinearMap_iff`

English:
theorem isIdempotentElem_toLinearMap_iff
  statement: {R M : Type*} [Semiring R] [TopologicalSpace M]
  proof: by
  simp only [IsIdempotentElem, Module.End.mul_eq_comp, ← toLinearMap_comp, mul_def, coe_inj]

alias ⟨_, IsIdempotentElem.toLinearMap⟩ := isIdempotentElem_toLinearMap_iff

中文:
定理 isIdempotentElem_toLinearMap_iff
  结论: {R M : 类型} [半环 R] [拓扑空间 M]
  证明: by
  simp only [IsIdempotentElem, Module.End.mul_eq_comp, ← toLinearMap_comp, mul_def, coe_inj]

alias ⟨_, IsIdempotentElem.toLinearMap⟩ := isIdempotentElem_toLinearMap_iff

Depends on / 依赖: IsIdempotentElem, Module, Module.End.mul_eq_comp, coe_inj, mul_def, mul_eq_comp, toLinearMap_comp
-/
theorem isIdempotentElem_toLinearMap_iff {R M : Type*} [Semiring R] [TopologicalSpace M]
    [AddCommMonoid M] [Module R M] {f : M ->L[R] M} :
    IsIdempotentElem f.toLinearMap ↔ IsIdempotentElem f := by
  simp only [IsIdempotentElem, Module.End.mul_eq_comp, ← toLinearMap_comp, mul_def, coe_inj]

alias ⟨_, IsIdempotentElem.toLinearMap⟩ := isIdempotentElem_toLinearMap_iff

variable {R M : Type*} [Ring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]

open ContinuousLinearMap

namespace IsIdempotentElem

/--
lemma `ext_iff` / 引理 `ext_iff`

English:
lemma ext_iff
  statement: {p q : M ->L[R] M}
  proof: by
  simpa using LinearMap.IsIdempotentElem.ext_iff hp.toLinearMap hq.toLinearMap

alias ⟨_, ext⟩ := IsIdempotentElem.ext_iff

中文:
引理 ext_iff
  结论: {p q : M ->L[R] M}
  证明: by
  simpa using LinearMap.IsIdempotentElem.ext_iff hp.toLinearMap hq.toLinearMap

alias ⟨_, ext⟩ := IsIdempotentElem.ext_iff

Depends on / 依赖: IsIdempotentElem, LinearMap, LinearMap.IsIdempotentElem.ext_iff, ext_iff, hp.toLinearMap, hq.toLinearMap, toLinearMap
-/
lemma ext_iff {p q : M ->L[R] M}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    p = q ↔ p.range = q.range ∧ p.ker = q.ker := by
  simpa using LinearMap.IsIdempotentElem.ext_iff hp.toLinearMap hq.toLinearMap

alias ⟨_, ext⟩ := IsIdempotentElem.ext_iff

/--
lemma `range_mem_invtSubmodule_iff` / 引理 `range_mem_invtSubmodule_iff`

English:
lemma range_mem_invtSubmodule_iff
  statement: {f T : M ->L[R] M}
  proof: by
  simpa [← toLinearMap_comp] using
    LinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨conj_eq_of_range_mem_invtSubmodule,
  range_mem_invtSubmodule⟩ := IsIdempotentElem.range_mem_invtSubmodule_iff

中文:
引理 range_mem_invtSubmodule_iff
  结论: {f T : M ->L[R] M}
  证明: by
  simpa [← toLinearMap_comp] using
    LinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨conj_eq_of_range_mem_invtSubmodule,
  range_mem_invtSubmodule⟩ := IsIdempotentElem.range_mem_invtSubmodule_iff

Depends on / 依赖: IsIdempotentElem, LinearMap, LinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff, hf.toLinearMap, range_mem_invtSubmodule_iff, toLinearMap, toLinearMap_comp
-/
lemma range_mem_invtSubmodule_iff {f T : M ->L[R] M}
    (hf : IsIdempotentElem f) :
    f.range in Module.End.invtSubmodule T ↔ f ∘L T ∘L f = T ∘L f := by
  simpa [← toLinearMap_comp] using
    LinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨conj_eq_of_range_mem_invtSubmodule,
  range_mem_invtSubmodule⟩ := IsIdempotentElem.range_mem_invtSubmodule_iff

/--
lemma `ker_mem_invtSubmodule_iff` / 引理 `ker_mem_invtSubmodule_iff`

English:
lemma ker_mem_invtSubmodule_iff
  statement: {f T : M ->L[R] M}
  proof: by
  simpa [← toLinearMap_comp] using
    LinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨conj_eq_of_ker_mem_invtSubmodule,
  ker_mem_invtSubmodule⟩ := IsIdempotentElem.ker_mem_invtSubmodule_iff

中文:
引理 ker_mem_invtSubmodule_iff
  结论: {f T : M ->L[R] M}
  证明: by
  simpa [← toLinearMap_comp] using
    LinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨conj_eq_of_ker_mem_invtSubmodule,
  ker_mem_invtSubmodule⟩ := IsIdempotentElem.ker_mem_invtSubmodule_iff

Depends on / 依赖: IsIdempotentElem, LinearMap, LinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff, hf.toLinearMap, ker_mem_invtSubmodule_iff, toLinearMap, toLinearMap_comp
-/
lemma ker_mem_invtSubmodule_iff {f T : M ->L[R] M}
    (hf : IsIdempotentElem f) :
    f.ker in Module.End.invtSubmodule T ↔ f ∘L T ∘L f = f ∘L T := by
  simpa [← toLinearMap_comp] using
    LinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨conj_eq_of_ker_mem_invtSubmodule,
  ker_mem_invtSubmodule⟩ := IsIdempotentElem.ker_mem_invtSubmodule_iff

/--
lemma `commute_iff` / 引理 `commute_iff`

English:
lemma commute_iff
  statement: {f T : M ->L[R] M}
  proof: by
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← toLinearMap_comp] using!
    LinearMap.IsIdempotentElem.commute_iff (T := T) hf.toLinearMap

中文:
引理 commute_iff
  结论: {f T : M ->L[R] M}
  证明: by
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← toLinearMap_comp] using!
    LinearMap.IsIdempotentElem.commute_iff (T := T) hf.toLinearMap

Depends on / 依赖: Commute, IsIdempotentElem, LinearMap, LinearMap.IsIdempotentElem.commute_iff, Module, Module.End.mul_eq_comp, SemiconjBy, commute_iff, hf.toLinearMap, mul_eq_comp, toLinearMap, toLinearMap_comp
-/
lemma commute_iff {f T : M ->L[R] M}
    (hf : IsIdempotentElem f) :
    Commute f T ↔ (f.range in Module.End.invtSubmodule T ∧ f.ker in Module.End.invtSubmodule T) := by
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← toLinearMap_comp] using!
    LinearMap.IsIdempotentElem.commute_iff (T := T) hf.toLinearMap

variable [IsTopologicalAddGroup M]

/--
theorem `commute_iff_of_isUnit` / 定理 `commute_iff_of_isUnit`

English:
theorem commute_iff_of_isUnit
  statement: {f T : M ->L[R] M} (hT : IsUnit T)
  proof: by
  have := hT.map ContinuousLinearMap.toLinearMapRingHom
  lift T to (M ->L[R] M)ˣ using hT
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← toLinearMap_comp] using!
    LinearMap.IsIdempotentElem.commute_iff_of_isUnit this hf.toLinearMap

中文:
定理 commute_iff_of_isUnit
  结论: {f T : M ->L[R] M} (hT : 是单位 T)
  证明: by
  have := hT.map ContinuousLinearMap.toLinearMapRingHom
  lift T to (M ->L[R] M)ˣ using hT
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← toLinearMap_comp] using!
    LinearMap.IsIdempotentElem.commute_iff_of_isUnit this hf.toLinearMap

Depends on / 依赖: Commute, ContinuousLinearMap, ContinuousLinearMap.toLinearMapRingHom, IsIdempotentElem, LinearMap, LinearMap.IsIdempotentElem.commute_iff_of_isUnit, Module, Module.End.mul_eq_comp, SemiconjBy, commute_iff_of_isUnit, hT.map, hf.toLinearMap, mul_eq_comp, toLinearMap, toLinearMapRingHom, toLinearMap_comp
-/
theorem commute_iff_of_isUnit {f T : M ->L[R] M} (hT : IsUnit T)
    (hf : IsIdempotentElem f) :
    Commute f T ↔ f.range.map (T : M ->ₗ[R] M) = f.range ∧ f.ker.map (T : M ->ₗ[R] M) = f.ker := by
  have := hT.map ContinuousLinearMap.toLinearMapRingHom
  lift T to (M ->L[R] M)ˣ using hT
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← toLinearMap_comp] using!
    LinearMap.IsIdempotentElem.commute_iff_of_isUnit this hf.toLinearMap

/--
theorem `isClosed_range` / 定理 `isClosed_range`

English:
theorem isClosed_range
  statement: [T1Space M] {p : M ->L[R] M}
  proof: LinearMap.IsIdempotentElem.range_eq_ker hp.toLinearMap ▸ isClosed_ker (.id R M - p)

中文:
定理 isClosed_range
  结论: [T1空间 M] {p : M ->L[R] M}
  证明: LinearMap.IsIdempotentElem.range_eq_ker hp.toLinearMap ▸ isClosed_ker (.id R M - p)

Depends on / 依赖: IsIdempotentElem, LinearMap, LinearMap.IsIdempotentElem.range_eq_ker, hp.toLinearMap, isClosed_ker, range_eq_ker, toLinearMap
-/
theorem isClosed_range [T1Space M] {p : M ->L[R] M}
    (hp : IsIdempotentElem p) : IsClosed (p.range : Set M) :=
  LinearMap.IsIdempotentElem.range_eq_ker hp.toLinearMap ▸ isClosed_ker (.id R M - p)

end IsIdempotentElem

end ContinuousLinearMap
