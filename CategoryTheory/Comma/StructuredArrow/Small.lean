/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# Small sets in the category of structured arrows

Here we prove a technical result about small sets in the category of structured arrows that will
be used in the proof of the Special Adjoint Functor Theorem.
-/

public section

namespace CategoryTheory

-- morphism levels before object levels. See note [category theory universes].
universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace StructuredArrow

variable {S : D} {T : C ⥤ D}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{w}
  signature: C] [LocallySmall.{w} D] : Small.{w} (StructuredArrow S T)
  body: small_of_surjective (f := fun (f : Σ (X : C), S ⟶ T.obj X) => StructuredArrow.mk f.2)
    (fun f => by
      obtain ⟨X, f, rfl⟩ := f.mk_surjective
      exact ⟨⟨X, f⟩, rfl⟩)

中文:
实例 [Small.{w}
  签名: C] [LocallySmall.{w} D] : Small.{w} (结构化箭头 S T)
  定义体: small_of_surjective (f := fun (f : Σ (X : C), S ⟶ T.obj X) => StructuredArrow.mk f.2)
    (fun f => by
      obtain ⟨X, f, rfl⟩ := f.mk_surjective
      exact ⟨⟨X, f⟩, rfl⟩)

Depends on / 依赖: Discrete, Discrete.functor, Discrete.natIso, F.obj, Functor, Functor.Final.colimitIso, Ind.colimitPresentationCompYoneda, Ind.yoneda, Pi.eval, StructuredArrow, StructuredArrow.mk, T.obj, colimitIso, colimitPresentationCompYoneda, f.mk_surjective, functor, mk_surjective, natIso, presentation, presentation.F
-/
instance [Small.{w} C] [LocallySmall.{w} D] : Small.{w} (StructuredArrow S T) :=
  small_of_surjective (f := fun (f : Σ (X : C), S ⟶ T.obj X) => StructuredArrow.mk f.2)
    (fun f => by
      obtain ⟨X, f, rfl⟩ := f.mk_surjective
      exact ⟨⟨X, f⟩, rfl⟩)

/--
Instance `small_inverseImage_proj_of_locallySmall` / 实例 `small_inverseImage_proj_of_locallySmall`

English:
instance small_inverseImage_proj_of_locallySmall
  body: by
  suffices P.inverseImage (proj S T) = .ofObj fun f : Σ (G : Subtype P), S ⟶ T.obj G => mk f.2 by
    rw [this]
    infer_instance
  ext X
  simp only [ObjectProperty.prop_inverseImage_iff, proj_obj, ObjectProperty.ofObj_iff,
    Sigma.exists, Subtype.exists, exists_prop]
  exact ⟨fun h => ⟨_, h, _, rfl⟩, by rintro ⟨_, h, _, rfl⟩; exact h⟩

中文:
实例 small_inverseImage_proj_of_locallySmall
  定义体: by
  suffices P.inverseImage (proj S T) = .ofObj fun f : Σ (G : Subtype P), S ⟶ T.obj G => mk f.2 by
    rw [this]
    infer_instance
  ext X
  simp only [ObjectProperty.prop_inverseImage_iff, proj_obj, ObjectProperty.ofObj_iff,
    Sigma.exists, Subtype.exists, exists_prop]
  exact ⟨fun h => ⟨_, h, _, rfl⟩, by rintro ⟨_, h, _, rfl⟩; exact h⟩

Depends on / 依赖: ObjectProperty, ObjectProperty.ofObj_iff, ObjectProperty.prop_inverseImage_iff, P.inverseImage, Sigma.exists, Subtype, Subtype.exists, T.obj, exists_prop, infer_instance, inverseImage, ofObj_iff, proj_obj, prop_inverseImage_iff
-/
instance small_inverseImage_proj_of_locallySmall
    {P : ObjectProperty C} [ObjectProperty.Small.{v₁} P] [LocallySmall.{v₁} D] :
    ObjectProperty.Small.{v₁} (P.inverseImage (proj S T)) := by
  suffices P.inverseImage (proj S T) = .ofObj fun f : Σ (G : Subtype P), S ⟶ T.obj G => mk f.2 by
    rw [this]
    infer_instance
  ext X
  simp only [ObjectProperty.prop_inverseImage_iff, proj_obj, ObjectProperty.ofObj_iff,
    Sigma.exists, Subtype.exists, exists_prop]
  exact ⟨fun h => ⟨_, h, _, rfl⟩, by rintro ⟨_, h, _, rfl⟩; exact h⟩

/--
Instance `essentiallySmall` / 实例 `essentiallySmall`

English:
instance essentiallySmall
  signature: [EssentiallySmall.{w} C] [LocallySmall.{w} D]
  body: by
  rw [← essentiallySmall_congr
    (StructuredArrow.pre S (equivSmallModel.{w} C).inverse T).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _

中文:
实例 essentiallySmall
  签名: [EssentiallySmall.{w} C] [LocallySmall.{w} D]
  定义体: by
  rw [← essentiallySmall_congr
    (StructuredArrow.pre S (equivSmallModel.{w} C).inverse T).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _

Depends on / 依赖: StructuredArrow, StructuredArrow.pre, asEquivalence, equivSmallModel, essentiallySmall_congr, essentiallySmall_of_small_of_locallySmall, inverse
-/
instance essentiallySmall [EssentiallySmall.{w} C] [LocallySmall.{w} D] :
    EssentiallySmall.{w} (StructuredArrow S T) := by
  rw [← essentiallySmall_congr
    (StructuredArrow.pre S (equivSmallModel.{w} C).inverse T).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _

end StructuredArrow

namespace CostructuredArrow

variable {S : C ⥤ D} {T : D}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{w}
  signature: C] [LocallySmall.{w} D] : Small.{w} (CostructuredArrow S T)
  body: small_of_surjective (f := fun (f : Σ (X : C), S.obj X ⟶ T) => CostructuredArrow.mk f.2)
    (fun f => by
      obtain ⟨X, f, rfl⟩ := f.mk_surjective
      exact ⟨⟨X, f⟩, rfl⟩)

中文:
实例 [Small.{w}
  签名: C] [LocallySmall.{w} D] : Small.{w} (CostructuredArrow S T)
  定义体: small_of_surjective (f := fun (f : Σ (X : C), S.obj X ⟶ T) => CostructuredArrow.mk f.2)
    (fun f => by
      obtain ⟨X, f, rfl⟩ := f.mk_surjective
      exact ⟨⟨X, f⟩, rfl⟩)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, S.obj, f.mk_surjective, mk_surjective, small_of_surjective
-/
instance [Small.{w} C] [LocallySmall.{w} D] : Small.{w} (CostructuredArrow S T) :=
  small_of_surjective (f := fun (f : Σ (X : C), S.obj X ⟶ T) => CostructuredArrow.mk f.2)
    (fun f => by
      obtain ⟨X, f, rfl⟩ := f.mk_surjective
      exact ⟨⟨X, f⟩, rfl⟩)

/--
Instance `small_inverseImage_proj_of_locallySmall` / 实例 `small_inverseImage_proj_of_locallySmall`

English:
instance small_inverseImage_proj_of_locallySmall
  body: by
  suffices P.inverseImage (proj S T) = .ofObj fun f : Σ (G : Subtype P), S.obj G ⟶ T => mk f.2 by
    rw [this]
    infer_instance
  ext X
  simp only [ObjectProperty.prop_inverseImage_iff, proj_obj, ObjectProperty.ofObj_iff,
    Sigma.exists, Subtype.exists, exists_prop]
  exact ⟨fun h => ⟨_, h, _, rfl⟩, by rintro ⟨_, h, _, rfl⟩; exact h⟩

中文:
实例 small_inverseImage_proj_of_locallySmall
  定义体: by
  suffices P.inverseImage (proj S T) = .ofObj fun f : Σ (G : Subtype P), S.obj G ⟶ T => mk f.2 by
    rw [this]
    infer_instance
  ext X
  simp only [ObjectProperty.prop_inverseImage_iff, proj_obj, ObjectProperty.ofObj_iff,
    Sigma.exists, Subtype.exists, exists_prop]
  exact ⟨fun h => ⟨_, h, _, rfl⟩, by rintro ⟨_, h, _, rfl⟩; exact h⟩

Depends on / 依赖: ObjectProperty, ObjectProperty.ofObj_iff, ObjectProperty.prop_inverseImage_iff, P.inverseImage, S.obj, Sigma.exists, Subtype, Subtype.exists, exists_prop, infer_instance, inverseImage, ofObj_iff, proj_obj, prop_inverseImage_iff
-/
instance small_inverseImage_proj_of_locallySmall
    {P : ObjectProperty C} [ObjectProperty.Small.{v₁} P] [LocallySmall.{v₁} D] :
    ObjectProperty.Small.{v₁} (P.inverseImage (proj S T)) := by
  suffices P.inverseImage (proj S T) = .ofObj fun f : Σ (G : Subtype P), S.obj G ⟶ T => mk f.2 by
    rw [this]
    infer_instance
  ext X
  simp only [ObjectProperty.prop_inverseImage_iff, proj_obj, ObjectProperty.ofObj_iff,
    Sigma.exists, Subtype.exists, exists_prop]
  exact ⟨fun h => ⟨_, h, _, rfl⟩, by rintro ⟨_, h, _, rfl⟩; exact h⟩

/--
Instance `essentiallySmall` / 实例 `essentiallySmall`

English:
instance essentiallySmall
  signature: [EssentiallySmall.{w} C] [LocallySmall.{w} D]
  body: by
  rw [← essentiallySmall_congr
    (CostructuredArrow.pre (equivSmallModel.{w} C).inverse S T).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _

中文:
实例 essentiallySmall
  签名: [EssentiallySmall.{w} C] [LocallySmall.{w} D]
  定义体: by
  rw [← essentiallySmall_congr
    (CostructuredArrow.pre (equivSmallModel.{w} C).inverse S T).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _

Depends on / 依赖: CostructuredArrow, CostructuredArrow.pre, asEquivalence, equivSmallModel, essentiallySmall_congr, essentiallySmall_of_small_of_locallySmall, inverse
-/
instance essentiallySmall [EssentiallySmall.{w} C] [LocallySmall.{w} D] :
    EssentiallySmall.{w} (CostructuredArrow S T) := by
  rw [← essentiallySmall_congr
    (CostructuredArrow.pre (equivSmallModel.{w} C).inverse S T).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _

end CostructuredArrow

end CategoryTheory
