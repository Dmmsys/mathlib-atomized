/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Generators in the category of presheaves

In this file, we show that if `A` is a category with zero morphisms that
has a separator (and suitable coproducts), then the category of
presheaves `Cᵒᵖ ⥤ A` also has a separator.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

namespace Presheaf

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{v} A]

/-- Given `X : C` and `M : A`, this is the presheaf `Cᵒᵖ ⥤ A` which sends
`Y : Cᵒᵖ` to the coproduct of copies of `M` indexed by `Y.unop ⟶ X`. -/
@[simps]
/--
Definition of `freeYoneda` / `freeYoneda` 的定义

English:
definition freeYoneda
  signature: (X : C) (M : A)
  body: ∐ (fun (i : (yoneda.obj X).obj Y) => M)
  map f := Sigma.map' ((yoneda.obj X).map f) (fun _ => 𝟙 M)

中文:
定义 freeYoneda
  签名: (X : C) (M : A)
  定义体: ∐ (fun (i : (yoneda.obj X).obj Y) => M)
  map f := Sigma.map' ((yoneda.obj X).map f) (fun _ => 𝟙 M)

Depends on / 依赖: HasSplitEqualizer, hasEqualizer_of_hasSplitEqualizer, yoneda, yoneda.obj
-/
noncomputable def freeYoneda (X : C) (M : A) : Cᵒᵖ ⥤ A where
  obj Y := ∐ (fun (i : (yoneda.obj X).obj Y) => M)
  map f := Sigma.map' ((yoneda.obj X).map f) (fun _ => 𝟙 M)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `freeYonedaHomEquiv` / `freeYonedaHomEquiv` 的定义

English:
definition freeYonedaHomEquiv
  signature: {X : C} {M : A} {F : Cᵒᵖ ⥤ A}
  body: Sigma.ι (fun (i : (yoneda.obj X).obj _) => M) (𝟙 _) ≫ f.app (op X)
  invFun g :=
    { app Y := Sigma.desc (fun φ => g ≫ F.map φ.op)
      naturality _ _ _ := Sigma.hom_ext _ _ (by simp) }
  left_inv f := by
    ext Y
    refine Sigma.hom_ext _ _ (fun φ => ?_)
    simpa using (Sigma.ι _ (𝟙 _) ≫= f.n

中文:
定义 freeYonedaHomEquiv
  签名: {X : C} {M : A} {F : Cᵒᵖ ⥤ A}
  定义体: Sigma.ι (fun (i : (yoneda.obj X).obj _) => M) (𝟙 _) ≫ f.app (op X)
  invFun g :=
    { app Y := Sigma.desc (fun φ => g ≫ F.map φ.op)
      naturality _ _ _ := Sigma.hom_ext _ _ (by simp) }
  left_inv f := by
    ext Y
    refine Sigma.hom_ext _ _ (fun φ => ?_)
    simpa using (Sigma.ι _ (𝟙 _) ≫= f.n

Depends on / 依赖: f.app, yoneda, yoneda.obj
-/
noncomputable def freeYonedaHomEquiv {X : C} {M : A} {F : Cᵒᵖ ⥤ A} :
    (freeYoneda X M ⟶ F) ≃ (M ⟶ F.obj (op X)) where
  toFun f := Sigma.ι (fun (i : (yoneda.obj X).obj _) => M) (𝟙 _) ≫ f.app (op X)
  invFun g :=
    { app Y := Sigma.desc (fun φ => g ≫ F.map φ.op)
      naturality _ _ _ := Sigma.hom_ext _ _ (by simp) }
  left_inv f := by
    ext Y
    refine Sigma.hom_ext _ _ (fun φ => ?_)
    simpa using (Sigma.ι _ (𝟙 _) ≫= f.naturality φ.op).symm
  right_inv g := by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `freeYonedaHomEquiv_comp` / 引理 `freeYonedaHomEquiv_comp`

English:
lemma freeYonedaHomEquiv_comp
  statement: {X : C} {M : A} {F G : Cᵒᵖ ⥤ A}
  proof: by
  simp [freeYonedaHomEquiv]

@[reassoc]

中文:
引理 freeYonedaHomEquiv_comp
  结论: {X : C} {M : A} {F G : Cᵒᵖ ⥤ A}
  证明: by
  simp [freeYonedaHomEquiv]

@[reassoc]

Depends on / 依赖: freeYonedaHomEquiv
-/
lemma freeYonedaHomEquiv_comp {X : C} {M : A} {F G : Cᵒᵖ ⥤ A}
    (α : freeYoneda X M ⟶ F) (f : F ⟶ G) :
    freeYonedaHomEquiv (α ≫ f) = freeYonedaHomEquiv α ≫ f.app (op X) := by
  simp [freeYonedaHomEquiv]

@[reassoc]
/--
lemma `freeYonedaHomEquiv_symm_comp` / 引理 `freeYonedaHomEquiv_symm_comp`

English:
lemma freeYonedaHomEquiv_symm_comp
  statement: {X : C} {M : A} {F G : Cᵒᵖ ⥤ A} (α : M ⟶ F.obj (op X))
  proof: by
  apply freeYonedaHomEquiv.injective
  simp only [freeYonedaHomEquiv_comp, Equiv.apply_symm_apply]

中文:
引理 freeYonedaHomEquiv_symm_comp
  结论: {X : C} {M : A} {F G : Cᵒᵖ ⥤ A} (α : M ⟶ F.obj (op X))
  证明: by
  apply freeYonedaHomEquiv.injective
  simp only [freeYonedaHomEquiv_comp, Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, freeYonedaHomEquiv, freeYonedaHomEquiv.injective, freeYonedaHomEquiv_comp, injective
-/
lemma freeYonedaHomEquiv_symm_comp {X : C} {M : A} {F G : Cᵒᵖ ⥤ A} (α : M ⟶ F.obj (op X))
    (f : F ⟶ G) :
    freeYonedaHomEquiv.symm α ≫ f = freeYonedaHomEquiv.symm (α ≫ f.app (op X)) := by
  apply freeYonedaHomEquiv.injective
  simp only [freeYonedaHomEquiv_comp, Equiv.apply_symm_apply]

variable (C)

/--
lemma `isSeparating` / 引理 `isSeparating`

English:
lemma isSeparating
  given: {ι : Type w} {S : ι -> A} (hS : ObjectProperty.IsSeparating (.ofObj S))
  proof: by
  intro F G f g h
  ext ⟨X⟩
  refine hS _ _ ?_
  rintro _ ⟨i⟩ α
  apply freeYonedaHomEquiv.symm.injective
  simpa only [freeYonedaHomEquiv_symm_comp] using
    h _ (ObjectProperty.ofObj_apply _ ⟨X, i⟩) (freeYonedaHomEquiv.symm α)

中文:
引理 isSeparating
  条件: {ι : Type w} {S : ι -> A} (hS : Object命题erty.IsSeparating (.ofObj S))
  证明: by
  intro F G f g h
  ext ⟨X⟩
  refine hS _ _ ?_
  rintro _ ⟨i⟩ α
  apply freeYonedaHomEquiv.symm.injective
  simpa only [freeYonedaHomEquiv_symm_comp] using
    h _ (ObjectProperty.ofObj_apply _ ⟨X, i⟩) (freeYonedaHomEquiv.symm α)

Depends on / 依赖: ObjectProperty, ObjectProperty.ofObj_apply, freeYonedaHomEquiv, freeYonedaHomEquiv.symm, freeYonedaHomEquiv.symm.injective, freeYonedaHomEquiv_symm_comp, injective, ofObj_apply
-/
lemma isSeparating {ι : Type w} {S : ι -> A} (hS : ObjectProperty.IsSeparating (.ofObj S)) :
    ObjectProperty.IsSeparating (.ofObj (fun (⟨X, i⟩ : C × ι) => freeYoneda X (S i))) := by
  intro F G f g h
  ext ⟨X⟩
  refine hS _ _ ?_
  rintro _ ⟨i⟩ α
  apply freeYonedaHomEquiv.symm.injective
  simpa only [freeYonedaHomEquiv_symm_comp] using
    h _ (ObjectProperty.ofObj_apply _ ⟨X, i⟩) (freeYonedaHomEquiv.symm α)

/--
lemma `isSeparator` / 引理 `isSeparator`

English:
lemma isSeparator
  statement: {ι : Type w} {S : ι -> A} (hS : ObjectProperty.IsSeparating (.ofObj S))
  proof: (isSeparating C hS).isSeparator_coproduct

中文:
引理 isSeparator
  结论: {ι : Type w} {S : ι -> A} (hS : Object命题erty.IsSeparating (.ofObj S))
  证明: (isSeparating C hS).isSeparator_coproduct

Depends on / 依赖: InitialMonoClass, initial_mono_of_strict_initial_objects, isSeparating, isSeparator_coproduct
-/
lemma isSeparator {ι : Type w} {S : ι -> A} (hS : ObjectProperty.IsSeparating (.ofObj S))
    [HasCoproduct (fun (⟨X, i⟩ : C × ι) => freeYoneda X (S i))]
    [HasZeroMorphisms A] :
    IsSeparator (∐ (fun (⟨X, i⟩ : C × ι) => freeYoneda X (S i))) :=
  (isSeparating C hS).isSeparator_coproduct

variable (A) in
/--
Instance `hasSeparator` / 实例 `hasSeparator`

English:
instance hasSeparator
  signature: [HasSeparator A] [HasZeroMorphisms A] [HasCoproducts.{u} A]
  body: ⟨_, isSeparator C (S := fun (_ : Unit) => separator A)
      (by simpa using! isSeparator_separator A)⟩

中文:
实例 hasSeparator
  签名: [HasSeparator A] [HasZeroMorphisms A] [HasCoproducts.{u} A]
  定义体: ⟨_, isSeparator C (S := fun (_ : Unit) => separator A)
      (by simpa using! isSeparator_separator A)⟩

Depends on / 依赖: isSeparator, separator
-/
instance hasSeparator [HasSeparator A] [HasZeroMorphisms A] [HasCoproducts.{u} A] :
    HasSeparator (Cᵒᵖ ⥤ A) where
  hasSeparator := ⟨_, isSeparator C (S := fun (_ : Unit) => separator A)
      (by simpa using! isSeparator_separator A)⟩

end Presheaf

end CategoryTheory
