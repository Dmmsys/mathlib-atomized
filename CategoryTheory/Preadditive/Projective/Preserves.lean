/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Preservation of projective objects

We define a typeclass `Functor.PreservesProjectiveObjects`.

We restate the existing result that if `F ⊣ G` is an adjunction and `G` preserves epimorphisms,
then `F` preserves projective objects. We show that the converse is true if the domain of `F` has
enough projectives.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/--
Definition of `Functor.PreservesProjectiveObjects` / `Functor.PreservesProjectiveObjects` 的定义

English:
class Functor.PreservesProjectiveObjects
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - projective_obj({X : C}) : Projective X -> Projective (F.obj X)

中文:
类 函子.保持ProjectiveObjects
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - projective_obj({X : C}) : 投射 X -> 投射 (F.obj X)
-/
class Functor.PreservesProjectiveObjects (F : C ⥤ D) : Prop where
  projective_obj {X : C} : Projective X -> Projective (F.obj X)

/--
Instance `Functor.projective_obj` / 实例 `Functor.projective_obj`

English:
instance Functor.projective_obj
  signature: (F : C ⥤ D) [F.PreservesProjectiveObjects] (X : C) [Projective X]
  body: Functor.PreservesProjectiveObjects.projective_obj inferInstance

中文:
实例 函子.projective_obj
  签名: (F : C ⥤ D) [F.保持ProjectiveObjects] (X : C) [投射 X]
  定义体: Functor.PreservesProjectiveObjects.projective_obj inferInstance

Depends on / 依赖: Functor, Functor.PreservesProjectiveObjects.projective_obj, PreservesProjectiveObjects, projective_obj
-/
instance Functor.projective_obj (F : C ⥤ D) [F.PreservesProjectiveObjects] (X : C) [Projective X] :
    Projective (F.obj X) :=
  Functor.PreservesProjectiveObjects.projective_obj inferInstance

/--
theorem `Functor.projective_obj_of_projective` / 定理 `Functor.projective_obj_of_projective`

English:
theorem Functor.projective_obj_of_projective
  statement: (F : C ⥤ D) [F.PreservesProjectiveObjects] {X : C}
  proof: Functor.PreservesProjectiveObjects.projective_obj h

中文:
定理 函子.projective_obj_of_projective
  结论: (F : C ⥤ D) [F.保持ProjectiveObjects] {X : C}
  证明: Functor.PreservesProjectiveObjects.projective_obj h

Depends on / 依赖: Functor, Functor.PreservesProjectiveObjects.projective_obj, PreservesProjectiveObjects, projective_obj
-/
theorem Functor.projective_obj_of_projective (F : C ⥤ D) [F.PreservesProjectiveObjects] {X : C}
    (h : Projective X) : Projective (F.obj X) :=
  Functor.PreservesProjectiveObjects.projective_obj h

/--
Instance `Functor.preservesProjectiveObjects_comp` / 实例 `Functor.preservesProjectiveObjects_comp`

English:
instance Functor.preservesProjectiveObjects_comp
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: G.projective_obj_of_projective ∘ F.projective_obj_of_projective

中文:
实例 函子.preservesProjectiveObjects_comp
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: G.projective_obj_of_projective ∘ F.projective_obj_of_projective

Depends on / 依赖: F.projective_obj_of_projective, G.projective_obj_of_projective, indiscrete, projective_obj_of_projective
-/
instance Functor.preservesProjectiveObjects_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesProjectiveObjects] [G.PreservesProjectiveObjects] :
    (F ⋙ G).PreservesProjectiveObjects where
  projective_obj := G.projective_obj_of_projective ∘ F.projective_obj_of_projective

/--
theorem `Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms` / 定理 `Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms`

English:
theorem Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
  proof: adj.map_projective _ h

中文:
定理 函子.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
  证明: adj.map_projective _ h

Depends on / 依赖: adj.map_projective, map_projective
-/
theorem Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.PreservesEpimorphisms] :
    F.PreservesProjectiveObjects where
  projective_obj h := adj.map_projective _ h

instance (priority := low) Functor.preservesProjectiveObjects_of_isEquivalence {F : C ⥤ D}
    [IsEquivalence F] : F.PreservesProjectiveObjects :=
  preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms F.asEquivalence.toAdjunction

/--
theorem `Functor.preservesEpimorphisms_of_adjunction_of_preservesProjectiveObjects` / 定理 `Functor.preservesEpimorphisms_of_adjunction_of_preservesProjectiveObjects`

English:
theorem Functor.preservesEpimorphisms_of_adjunction_of_preservesProjectiveObjects
  proof: by
    suffices exists h, h ≫ G.map f = Projective.π (G.obj Y) from epi_of_epi_fac this.choose_spec
    refine ⟨adj.unit.app (Projective.over (G.obj Y)) ≫
      G.map (Projective.factorThru (F.map (Projective.π _) ≫ adj.counit.app Y) f), ?_⟩
    rw [Category.assoc]; rw [← Functor.map_comp]
    simp

中文:
定理 函子.preservesEpimorphisms_of_adjunction_of_preservesProjectiveObjects
  证明: by
    suffices exists h, h ≫ G.map f = Projective.π (G.obj Y) from epi_of_epi_fac this.choose_spec
    refine ⟨adj.unit.app (Projective.over (G.obj Y)) ≫
      G.map (Projective.factorThru (F.map (Projective.π _) ≫ adj.counit.app Y) f), ?_⟩
    rw [Category.assoc]; rw [← Functor.map_comp]
    simp

Depends on / 依赖: Category, Category.assoc, F.map, Functor, Functor.map_comp, G.map, G.obj, Projective, Projective.factorThru, Projective.over, adj.counit.app, adj.unit.app, choose_spec, counit, epi_of_epi_fac, factorThru, map_comp, this.choose_spec
-/
theorem Functor.preservesEpimorphisms_of_adjunction_of_preservesProjectiveObjects
    [EnoughProjectives C] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.PreservesProjectiveObjects] :
    G.PreservesEpimorphisms where
  preserves {X Y} f _ := by
    suffices exists h, h ≫ G.map f = Projective.π (G.obj Y) from epi_of_epi_fac this.choose_spec
    refine ⟨adj.unit.app (Projective.over (G.obj Y)) ≫
      G.map (Projective.factorThru (F.map (Projective.π _) ≫ adj.counit.app Y) f), ?_⟩
    rw [Category.assoc]; rw [← Functor.map_comp]
    simp

end CategoryTheory
