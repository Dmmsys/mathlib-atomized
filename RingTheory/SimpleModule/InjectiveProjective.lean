/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Projective

/-!
If `R` is a semisimple ring, then any `R`-module is both injective and projective.

-/

public section

namespace Module

variable (R : Type*) [Ring R] [IsSemisimpleRing R] (M : Type*) [AddCommGroup M] [Module R M]

/--
theorem `injective_of_isSemisimpleRing` / 定理 `injective_of_isSemisimpleRing`

English:
theorem injective_of_isSemisimpleRing
  statement: Module.Injective R M where
  proof: let ⟨h, comp⟩ := IsSemisimpleModule.extension_property f hf g
    ⟨h, fun _ => by rw [← comp, LinearMap.comp_apply]⟩

中文:
定理 injective_of_isSemisimpleRing
  结论: 模.单射 R M where
  证明: let ⟨h, comp⟩ := IsSemisimpleModule.extension_property f hf g
    ⟨h, fun _ => by rw [← comp, LinearMap.comp_apply]⟩

Depends on / 依赖: IsSemisimpleModule, IsSemisimpleModule.extension_property, LinearMap, LinearMap.comp_apply, comp_apply, extension_property
-/
theorem injective_of_isSemisimpleRing : Module.Injective R M where
  out X Y _ _ _ _ f hf g :=
    let ⟨h, comp⟩ := IsSemisimpleModule.extension_property f hf g
    ⟨h, fun _ => by rw [← comp, LinearMap.comp_apply]⟩

/--
theorem `projective_of_isSemisimpleRing` / 定理 `projective_of_isSemisimpleRing`

English:
theorem projective_of_isSemisimpleRing
  statement: Module.Projective R M
  proof: .of_lifting_property'' (IsSemisimpleModule.lifting_property · · _)

中文:
定理 projective_of_isSemisimpleRing
  结论: 模.投射 R M
  证明: .of_lifting_property'' (IsSemisimpleModule.lifting_property · · _)

Depends on / 依赖: IsSemisimpleModule, IsSemisimpleModule.lifting_property, lifting_property, of_lifting_property
-/
theorem projective_of_isSemisimpleRing : Module.Projective R M :=
  .of_lifting_property'' (IsSemisimpleModule.lifting_property · · _)

end Module
