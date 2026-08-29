/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Set.Countable
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Countable modules
-/

public section

noncomputable section

namespace Finsupp

variable {M : Type*} {R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- If `R` is countable, then any `R`-submodule spanned by a countable family of vectors is
countable. -/
instance {ι : Type*} [Countable R] [Countable ι] (v : ι -> M) :
    Countable (Submodule.span R (Set.range v)) := by
  refine Set.countable_coe_iff.mpr (Set.Countable.mono ?_ (Set.countable_range
      (fun c : (ι ->₀ R) => c.sum fun i _ => (c i) • v i)))
  exact fun _ h => Finsupp.mem_span_range_iff_exists_finsupp.mp (SetLike.mem_coe.mp h)

/--
theorem `Countable.of_moduleFinite` / 定理 `Countable.of_moduleFinite`

English:
theorem Countable.of_moduleFinite
  given: [Countable R] [Module.Finite R M]
  statement: Countable M
  proof: by
  obtain ⟨n, s, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  rw [← Set.countable_univ_iff]
  have : Countable (Submodule.span R (Set.range s)) := inferInstance
  rwa [h] at this

中文:
定理 Countable.of_moduleFinite
  条件: [Countable R] [Module.Finite R M]
  结论: Countable M
  证明: by
  obtain ⟨n, s, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  rw [← Set.countable_univ_iff]
  have : Countable (Submodule.span R (Set.range s)) := inferInstance
  rwa [h] at this

Depends on / 依赖: Countable, Finite, Module, Module.Finite.exists_fin, Set.countable_univ_iff, Set.range, Submodule, Submodule.span, countable_univ_iff, exists_fin
-/
theorem Countable.of_moduleFinite [Countable R] [Module.Finite R M] : Countable M := by
  obtain ⟨n, s, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  rw [← Set.countable_univ_iff]
  have : Countable (Submodule.span R (Set.range s)) := inferInstance
  rwa [h] at this

/--
theorem `Uncountable.of_moduleFinite` / 定理 `Uncountable.of_moduleFinite`

English:
theorem Uncountable.of_moduleFinite
  given: [hM : Uncountable M] [Module.Finite R M]
  statement: Uncountable R
  proof: by
  by_contra!
exact (uncountable_iff_not_countable _).mp hM Countable.of_moduleFinite (R := R)

中文:
定理 Uncountable.of_moduleFinite
  条件: [hM : Uncountable M] [Module.Finite R M]
  结论: Uncountable R
  证明: by
  by_contra!
exact (uncountable_iff_not_countable _).mp hM Countable.of_moduleFinite (R := R)

Depends on / 依赖: Countable, Countable.of_moduleFinite, of_moduleFinite, uncountable_iff_not_countable
-/
theorem Uncountable.of_moduleFinite [hM : Uncountable M] [Module.Finite R M] : Uncountable R := by
  by_contra!
exact (uncountable_iff_not_countable _).mp hM Countable.of_moduleFinite (R := R)

end Finsupp
