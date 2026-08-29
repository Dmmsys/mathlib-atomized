/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Preservation of injective objects

We define a typeclass `Functor.PreservesInjectiveObjects`.

We restate the existing result that if `F ⊣ G` is an adjunction and `F` preserves monomorphisms,
then `G` preserves injective objects. We show that the converse is true if the codomain of `F` has
enough injectives.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/--
Definition of `Functor.PreservesInjectiveObjects` / `Functor.PreservesInjectiveObjects` 的定义

English:
class Functor.PreservesInjectiveObjects
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - injective_obj({X : C}) : Injective X -> Injective (F.obj X)

中文:
类 Functor.PreservesInjectiveObjects
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - injective_obj({X : C}) : Injective X -> Injective (F.obj X)
-/
class Functor.PreservesInjectiveObjects (F : C ⥤ D) : Prop where
  injective_obj {X : C} : Injective X -> Injective (F.obj X)

/--
Instance `Functor.injective_obj` / 实例 `Functor.injective_obj`

English:
instance Functor.injective_obj
  signature: (F : C ⥤ D) [F.PreservesInjectiveObjects] (X : C) [Injective X]
  body: Functor.PreservesInjectiveObjects.injective_obj inferInstance

中文:
实例 Functor.injective_obj
  签名: (F : C ⥤ D) [F.PreservesInjectiveObjects] (X : C) [Injective X]
  定义体: Functor.PreservesInjectiveObjects.injective_obj inferInstance

Depends on / 依赖: Functor, Functor.PreservesInjectiveObjects.injective_obj, PreservesInjectiveObjects, injective_obj
-/
instance Functor.injective_obj (F : C ⥤ D) [F.PreservesInjectiveObjects] (X : C) [Injective X] :
    Injective (F.obj X) :=
  Functor.PreservesInjectiveObjects.injective_obj inferInstance

/--
theorem `Functor.injective_obj_of_injective` / 定理 `Functor.injective_obj_of_injective`

English:
theorem Functor.injective_obj_of_injective
  statement: (F : C ⥤ D) [F.PreservesInjectiveObjects] {X : C}
  proof: Functor.PreservesInjectiveObjects.injective_obj h

中文:
定理 Functor.injective_obj_of_injective
  结论: (F : C ⥤ D) [F.PreservesInjectiveObjects] {X : C}
  证明: Functor.PreservesInjectiveObjects.injective_obj h

Depends on / 依赖: Functor, Functor.PreservesInjectiveObjects.injective_obj, PreservesInjectiveObjects, injective_obj
-/
theorem Functor.injective_obj_of_injective (F : C ⥤ D) [F.PreservesInjectiveObjects] {X : C}
    (h : Injective X) : Injective (F.obj X) :=
  Functor.PreservesInjectiveObjects.injective_obj h

/--
Instance `Functor.preservesInjectiveObjects_comp` / 实例 `Functor.preservesInjectiveObjects_comp`

English:
instance Functor.preservesInjectiveObjects_comp
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: G.injective_obj_of_injective ∘ F.injective_obj_of_injective

中文:
实例 Functor.preservesInjectiveObjects_comp
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: G.injective_obj_of_injective ∘ F.injective_obj_of_injective

Depends on / 依赖: F.injective_obj_of_injective, G.injective_obj_of_injective, injective_obj_of_injective
-/
instance Functor.preservesInjectiveObjects_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects] :
    (F ⋙ G).PreservesInjectiveObjects where
  injective_obj := G.injective_obj_of_injective ∘ F.injective_obj_of_injective

/--
theorem `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms` / 定理 `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`

English:
theorem Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
  proof: adj.map_injective _ h

中文:
定理 Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
  证明: adj.map_injective _ h

Depends on / 依赖: adj.map_injective, map_injective
-/
theorem Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.PreservesMonomorphisms] :
    G.PreservesInjectiveObjects where
  injective_obj h := adj.map_injective _ h

instance (priority := low) Functor.preservesInjectiveObjects_of_isEquivalence {F : C ⥤ D}
    [IsEquivalence F] : F.PreservesInjectiveObjects :=
  preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    F.asEquivalence.symm.toAdjunction

/--
theorem `Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects` / 定理 `Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects`

English:
theorem Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
  proof: by
    suffices exists h, F.map f ≫ h = Injective.ι (F.obj X) from mono_of_mono_fac this.choose_spec
    exact ⟨F.map (Injective.factorThru (adj.unit.app X ≫ G.map (Injective.ι _)) f) ≫
      adj.counit.app (Injective.under (F.obj X)), by simp [← Functor.map_comp_assoc]⟩

中文:
定理 Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
  证明: by
    suffices exists h, F.map f ≫ h = Injective.ι (F.obj X) from mono_of_mono_fac this.choose_spec
    exact ⟨F.map (Injective.factorThru (adj.unit.app X ≫ G.map (Injective.ι _)) f) ≫
      adj.counit.app (Injective.under (F.obj X)), by simp [← Functor.map_comp_assoc]⟩

Depends on / 依赖: F.map, F.obj, Functor, Functor.map_comp_assoc, G.map, Injective, Injective.factorThru, Injective.under, adj.counit.app, adj.unit.app, choose_spec, counit, factorThru, map_comp_assoc, mono_of_mono_fac, this.choose_spec
-/
theorem Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
    [EnoughInjectives D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.PreservesInjectiveObjects] :
    F.PreservesMonomorphisms where
  preserves {X Y} f _ := by
    suffices exists h, F.map f ≫ h = Injective.ι (F.obj X) from mono_of_mono_fac this.choose_spec
    exact ⟨F.map (Injective.factorThru (adj.unit.app X ≫ G.map (Injective.ι _)) f) ≫
      adj.counit.app (Injective.under (F.obj X)), by simp [← Functor.map_comp_assoc]⟩

end CategoryTheory
