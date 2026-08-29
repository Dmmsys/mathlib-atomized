/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Jujian Zhang
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Category of sheaves is abelian

Let `C, D` be categories and `J` be a Grothendieck topology on `C`, when `D` is abelian and
sheafification is possible in `C`, `Sheaf J D` is abelian as well (`sheafIsAbelian`).

Hence, `presheafToSheaf` is an additive functor (`presheafToSheaf_additive`).

-/

public section


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

section Abelian

universe w' w v u

variable {C : Type u} [Category.{v} C]
variable {D : Type w} [Category.{w'} D] [Abelian D]
variable {J : GrothendieckTopology C}
variable [HasSheafify J D]

/--
Instance `sheafIsAbelian` / 实例 `sheafIsAbelian`

English:
instance sheafIsAbelian
  signature: : Abelian (Sheaf J D)
  body: let adj := sheafificationAdjunction J D
  abelianOfAdjunction _ _ (asIso adj.counit) adj

中文:
实例 sheafIsAbelian
  签名: : 交换 (层 J D)
  定义体: let adj := sheafificationAdjunction J D
  abelianOfAdjunction _ _ (asIso adj.counit) adj

Depends on / 依赖: abelianOfAdjunction, adj.counit, counit, sheafificationAdjunction
-/
instance sheafIsAbelian : Abelian (Sheaf J D) :=
  let adj := sheafificationAdjunction J D
  abelianOfAdjunction _ _ (asIso adj.counit) adj

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

/--
Instance `presheafToSheaf_additive` / 实例 `presheafToSheaf_additive`

English:
instance presheafToSheaf_additive
  signature: : (presheafToSheaf J D).Additive
  body: (presheafToSheaf J D).additive_of_preservesBinaryBiproducts

中文:
实例 presheafToSheaf_additive
  签名: : (presheafToSheaf J D).加性
  定义体: (presheafToSheaf J D).additive_of_preservesBinaryBiproducts

Depends on / 依赖: additive_of_preservesBinaryBiproducts, presheafToSheaf
-/
instance presheafToSheaf_additive : (presheafToSheaf J D).Additive :=
  (presheafToSheaf J D).additive_of_preservesBinaryBiproducts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Functor.const Cᵒᵖ : D ⥤ Cᵒᵖ ⥤ D).Additive

中文:
实例 :
  签名: (函子.const Cᵒᵖ : D ⥤ Cᵒᵖ ⥤ D).加性
-/
instance : (Functor.const Cᵒᵖ : D ⥤ Cᵒᵖ ⥤ D).Additive where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (constantSheaf J D).Additive
  body: inferInstanceAs (Functor.const _ ⋙ presheafToSheaf _ _).Additive

中文:
实例 :
  签名: (constantSheaf J D).加性
  定义体: inferInstanceAs (Functor.const _ ⋙ presheafToSheaf _ _).Additive

Depends on / 依赖: Additive, Functor, Functor.const, presheafToSheaf
-/
instance : (constantSheaf J D).Additive :=
  inferInstanceAs (Functor.const _ ⋙ presheafToSheaf _ _).Additive

end Abelian

end CategoryTheory
