/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Module.Presentation.Basic
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Characterization of finitely presented modules

A module is finitely presented (in the sense of `Module.FinitePresentation`) iff
it admits a presentation with finitely many generators and relations.

-/

public section

universe w₀ w₁ v u

namespace Module

variable {A : Type u} [Ring A] {M : Type v} [AddCommGroup M] [Module A M]

namespace Presentation

variable (pres : Presentation A M)

/--
lemma `finite` / 引理 `finite`

English:
lemma finite
  given: [Finite pres.G]
  proof: Finite.of_surjective _ pres.surjective_π

中文:
引理 finite
  条件: [有限 pres.G]
  证明: Finite.of_surjective _ pres.surjective_π

Depends on / 依赖: Finite, Finite.of_surjective, of_surjective, pres.surjective_
-/
lemma finite [Finite pres.G] :
    Module.Finite A M :=
  Finite.of_surjective _ pres.surjective_π

/--
lemma `finitePresentation` / 引理 `finitePresentation`

English:
lemma finitePresentation
  given: [Finite pres.G] [Finite pres.R]
  proof: Module.finitePresentation_of_surjective _ pres.surjective_π (by
    rw [pres.ker_π]
    exact Submodule.fg_span (Set.finite_range _))

中文:
引理 finitePresentation
  条件: [有限 pres.G] [有限 pres.R]
  证明: Module.finitePresentation_of_surjective _ pres.surjective_π (by
    rw [pres.ker_π]
    exact Submodule.fg_span (Set.finite_range _))

Depends on / 依赖: Module, Module.finitePresentation_of_surjective, Set.finite_range, Submodule, Submodule.fg_span, fg_span, finitePresentation_of_surjective, finite_range, pres.ker_, pres.surjective_
-/
lemma finitePresentation [Finite pres.G] [Finite pres.R] :
    Module.FinitePresentation A M :=
  Module.finitePresentation_of_surjective _ pres.surjective_π (by
    rw [pres.ker_π]
    exact Submodule.fg_span (Set.finite_range _))

end Presentation

/--
lemma `finitePresentation_iff_exists_presentation` / 引理 `finitePresentation_iff_exists_presentation`

English:
lemma finitePresentation_iff_exists_presentation
  proof: by
  constructor
  · intro
    obtain ⟨G : Type w₀, _, var, hG⟩ :=
      Submodule.fg_iff_exists_finite_generating_family.1
        (finite_def.1 (inferInstance : Module.Finite A M))
    obtain ⟨R : Type w₁, _, relation, hR⟩ :=
      Submodule.fg_iff_exists_finite_generating_family.1
        (Module

中文:
引理 finitePresentation_iff_存在_presentation
  证明: by
  constructor
  · intro
    obtain ⟨G : Type w₀, _, var, hG⟩ :=
      Submodule.fg_iff_exists_finite_generating_family.1
        (finite_def.1 (inferInstance : Module.Finite A M))
    obtain ⟨R : Type w₁, _, relation, hR⟩ :=
      Submodule.fg_iff_exists_finite_generating_family.1
        (Module

Depends on / 依赖: Finite, FinitePresentation, Finsupp, Finsupp.linearCombination, Finsupp.range_linearCombination, LinearMap, LinearMap.range_eq_top, Module, Module.Finite, Module.FinitePresentation.fg_ker, Submodule, Submodule.fg_iff_exists_finite_generating_family, fg_iff_exists_finite_generating_family, fg_ker, finite_def, linearCombination, linearCombination_var_relation, range_eq_top, range_linearCombination, relation
-/
lemma finitePresentation_iff_exists_presentation :
    Module.FinitePresentation A M ↔
      exists (pres : Presentation.{w₀, w₁} A M), Finite pres.G ∧ Finite pres.R := by
  constructor
  · intro
    obtain ⟨G : Type w₀, _, var, hG⟩ :=
      Submodule.fg_iff_exists_finite_generating_family.1
        (finite_def.1 (inferInstance : Module.Finite A M))
    obtain ⟨R : Type w₁, _, relation, hR⟩ :=
      Submodule.fg_iff_exists_finite_generating_family.1
        (Module.FinitePresentation.fg_ker (Finsupp.linearCombination A var) (by
          rw [← LinearMap.range_eq_top]; rw [Finsupp.range_linearCombination]; rw [hG]))
    exact
     ⟨{ G := G
        R := R
        relation := relation
        var := var
        linearCombination_var_relation := fun r => by
          rw [Submodule.ext_iff] at hR
          exact (hR _).1 (Submodule.subset_span ⟨_, rfl⟩)
        toIsPresentation := by
          rw [Relations.Solution.isPresentation_iff]
          exact ⟨hG, hR.symm⟩ },
        inferInstance, inferInstance⟩
  · rintro ⟨pres, _, _⟩
    exact pres.finitePresentation

end Module
