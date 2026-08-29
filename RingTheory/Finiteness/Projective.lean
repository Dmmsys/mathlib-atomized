/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite and projective modules

-/

public section

open Function (Surjective)

namespace Module

namespace Finite

open Submodule Set

variable {R M N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable (R M) in
/--
theorem `exists_comp_eq_id_of_projective` / 定理 `exists_comp_eq_id_of_projective`

English:
theorem exists_comp_eq_id_of_projective
  given: [Module.Finite R M] [Projective R M]
  proof: have ⟨n, f, surj⟩ := exists_fin' R M
  have ⟨g, hfg⟩ := Module.projective_lifting_property f .id surj
  ⟨n, f, g, surj, LinearMap.injective_of_comp_eq_id _ _ hfg, hfg⟩

中文:
定理 存在_comp_eq_id_of_projective
  条件: [模.有限 R M] [投射 R M]
  证明: have ⟨n, f, surj⟩ := exists_fin' R M
  have ⟨g, hfg⟩ := Module.projective_lifting_property f .id surj
  ⟨n, f, g, surj, LinearMap.injective_of_comp_eq_id _ _ hfg, hfg⟩

Depends on / 依赖: LinearMap, LinearMap.injective_of_comp_eq_id, Module, Module.projective_lifting_property, exists_fin, injective_of_comp_eq_id, projective_lifting_property
-/
theorem exists_comp_eq_id_of_projective [Module.Finite R M] [Projective R M] :
    exists (n : Nat) (f : (Fin n -> R) ->ₗ[R] M) (g : M ->ₗ[R] Fin n -> R),
      Function.Surjective f ∧ Function.Injective g ∧ f ∘ₗ g = .id :=
  have ⟨n, f, surj⟩ := exists_fin' R M
  have ⟨g, hfg⟩ := Module.projective_lifting_property f .id surj
  ⟨n, f, g, surj, LinearMap.injective_of_comp_eq_id _ _ hfg, hfg⟩

end Finite

end Module
