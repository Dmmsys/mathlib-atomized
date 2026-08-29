/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finiteness of the powerset of a finite set

## Implementation notes

Each result in this file should come in three forms: a `Fintype` instance, a `Finite` instance
and a `Set.Finite` constructor.

## Tags

finite sets
-/

public section

assert_not_exists IsOrderedRing MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the `Fintype` module.

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

/--
theorem `Finite.finite_subsets` / 定理 `Finite.finite_subsets`

English:
theorem Finite.finite_subsets
  given: {α : Type u} {a : Set α} (h : a.Finite)
  statement: { b | b subseteq a }.Finite
  proof: by
  convert! ((Finset.powerset h.toFinset).map Finset.coeEmb.1).finite_toSet
  ext s
  simpa [← @exists_finite_iff_finset α fun t => t subseteq a ∧ t = s, Finite.subset_toFinset,
    ← and_assoc, Finset.coeEmb] using h.subset

中文:
定理 有限.finite_subsets
  条件: {α : 类型u} {a : 集合 α} (h : a.有限)
  结论: { b | b subseteq a }.有限
  证明: by
  convert! ((Finset.powerset h.toFinset).map Finset.coeEmb.1).finite_toSet
  ext s
  simpa [← @exists_finite_iff_finset α fun t => t subseteq a ∧ t = s, Finite.subset_toFinset,
    ← and_assoc, Finset.coeEmb] using h.subset

Depends on / 依赖: Finite, Finite.subset_toFinset, Finset, Finset.coeEmb, Finset.powerset, and_assoc, coeEmb, convert, exists_finite_iff_finset, finite_toSet, h.subset, h.toFinset, powerset, subset, subset_toFinset, subseteq, toFinset
-/
theorem Finite.finite_subsets {α : Type u} {a : Set α} (h : a.Finite) : { b | b subseteq a }.Finite := by
  convert! ((Finset.powerset h.toFinset).map Finset.coeEmb.1).finite_toSet
  ext s
  simpa [← @exists_finite_iff_finset α fun t => t subseteq a ∧ t = s, Finite.subset_toFinset,
    ← and_assoc, Finset.coeEmb] using h.subset

/--
theorem `Finite.powerset` / 定理 `Finite.powerset`

English:
theorem Finite.powerset
  given: {s : Set α} (h : s.Finite)
  statement: (𝒫 s).Finite
  proof: h.finite_subsets

中文:
定理 有限.powerset
  条件: {s : 集合 α} (h : s.有限)
  结论: (𝒫 s).有限
  证明: h.finite_subsets
-/
protected theorem Finite.powerset {s : Set α} (h : s.Finite) : (𝒫 s).Finite :=
  h.finite_subsets

end SetFiniteConstructors

end Set
