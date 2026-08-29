/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Generator.Presheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Generators in the category of sheaves

In this file, we show that if `J : GrothendieckTopology C` and `A` is a preadditive
category which has a separator (and suitable coproducts), then `Sheaf J A` has a separator.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

namespace Sheaf

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C) {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{v} A] [HasWeakSheafify J A]

/--
Definition of `freeYoneda` / `freeYoneda` 的定义

English:
definition freeYoneda
  signature: (X : C) (M : A)
  body: (presheafToSheaf J A).obj (Presheaf.freeYoneda X M)

中文:
定义 freeYoneda
  签名: (X : C) (M : A)
  定义体: (presheafToSheaf J A).obj (Presheaf.freeYoneda X M)

Depends on / 依赖: Presheaf, Presheaf.freeYoneda, freeYoneda, presheafToSheaf
-/
noncomputable def freeYoneda (X : C) (M : A) : Sheaf J A :=
  (presheafToSheaf J A).obj (Presheaf.freeYoneda X M)

variable {J} in
/--
Definition of `freeYonedaHomEquiv` / `freeYonedaHomEquiv` 的定义

English:
definition freeYonedaHomEquiv
  signature: {X : C} {M : A} {F : Sheaf J A}
  body: ((sheafificationAdjunction J A).homEquiv _ _).trans Presheaf.freeYonedaHomEquiv

中文:
定义 freeYonedaHomEquiv
  签名: {X : C} {M : A} {F : Sheaf J A}
  定义体: ((sheafificationAdjunction J A).homEquiv _ _).trans Presheaf.freeYonedaHomEquiv

Depends on / 依赖: Presheaf, Presheaf.freeYonedaHomEquiv, freeYonedaHomEquiv, homEquiv, sheafificationAdjunction
-/
noncomputable def freeYonedaHomEquiv {X : C} {M : A} {F : Sheaf J A} :
    (freeYoneda J X M ⟶ F) ≃ (M ⟶ F.obj.obj (op X)) :=
  ((sheafificationAdjunction J A).homEquiv _ _).trans Presheaf.freeYonedaHomEquiv

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isSeparating` / 引理 `isSeparating`

English:
lemma isSeparating
  given: {ι : Type w} {S : ι -> A} (hS : ObjectProperty.IsSeparating (.ofObj S))
  proof: by
  intro F G f g hfg
  refine (sheafToPresheaf J A).map_injective (Presheaf.isSeparating C hS _ _ ?_)
  rintro _ ⟨X, i⟩ a
  apply ((sheafificationAdjunction _ _).homEquiv _ _).symm.injective
  simpa only [← Adjunction.homEquiv_naturality_right_symm] using
    hfg _ (ObjectProperty.ofObj_apply _ ⟨X

中文:
引理 isSeparating
  条件: {ι : Type w} {S : ι -> A} (hS : Object命题erty.IsSeparating (.ofObj S))
  证明: by
  intro F G f g hfg
  refine (sheafToPresheaf J A).map_injective (Presheaf.isSeparating C hS _ _ ?_)
  rintro _ ⟨X, i⟩ a
  apply ((sheafificationAdjunction _ _).homEquiv _ _).symm.injective
  simpa only [← Adjunction.homEquiv_naturality_right_symm] using
    hfg _ (ObjectProperty.ofObj_apply _ ⟨X

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_right_symm, ObjectProperty, ObjectProperty.ofObj_apply, Presheaf, Presheaf.isSeparating, homEquiv, homEquiv_naturality_right_symm, injective, isSeparating, map_injective, ofObj_apply, sheafToPresheaf, sheafificationAdjunction, symm.injective
-/
lemma isSeparating {ι : Type w} {S : ι -> A} (hS : ObjectProperty.IsSeparating (.ofObj S)) :
    ObjectProperty.IsSeparating (.ofObj (fun (⟨X, i⟩ : C × ι) => freeYoneda J X (S i))) := by
  intro F G f g hfg
  refine (sheafToPresheaf J A).map_injective (Presheaf.isSeparating C hS _ _ ?_)
  rintro _ ⟨X, i⟩ a
  apply ((sheafificationAdjunction _ _).homEquiv _ _).symm.injective
  simpa only [← Adjunction.homEquiv_naturality_right_symm] using
    hfg _ (ObjectProperty.ofObj_apply _ ⟨X, i⟩)
      (((sheafificationAdjunction _ _).homEquiv _ _).symm a)

/--
lemma `isSeparator` / 引理 `isSeparator`

English:
lemma isSeparator
  statement: {ι : Type w} {S : ι -> A} (hS : ObjectProperty.IsSeparating (.ofObj S))
  proof: (isSeparating J hS).isSeparator_coproduct

中文:
引理 isSeparator
  结论: {ι : Type w} {S : ι -> A} (hS : Object命题erty.IsSeparating (.ofObj S))
  证明: (isSeparating J hS).isSeparator_coproduct

Depends on / 依赖: isSeparating, isSeparator_coproduct
-/
lemma isSeparator {ι : Type w} {S : ι -> A} (hS : ObjectProperty.IsSeparating (.ofObj S))
    [HasCoproduct (fun (⟨X, i⟩ : C × ι) => freeYoneda J X (S i))] [Preadditive A] :
    IsSeparator (∐ (fun (⟨X, i⟩ : C × ι) => freeYoneda J X (S i))) :=
  (isSeparating J hS).isSeparator_coproduct

variable (A) in
/--
Instance `hasSeparator` / 实例 `hasSeparator`

English:
instance hasSeparator
  signature: [HasSeparator A] [Preadditive A] [HasCoproducts.{u} A]
  body: ⟨_, isSeparator J (S := fun (_ : Unit) => separator A)
      (by simpa using! isSeparator_separator A)⟩

中文:
实例 hasSeparator
  签名: [HasSeparator A] [Preadditive A] [HasCoproducts.{u} A]
  定义体: ⟨_, isSeparator J (S := fun (_ : Unit) => separator A)
      (by simpa using! isSeparator_separator A)⟩

Depends on / 依赖: isSeparator, separator
-/
instance hasSeparator [HasSeparator A] [Preadditive A] [HasCoproducts.{u} A] :
    HasSeparator (Sheaf J A) where
  hasSeparator := ⟨_, isSeparator J (S := fun (_ : Unit) => separator A)
      (by simpa using! isSeparator_separator A)⟩

end Sheaf

end CategoryTheory
