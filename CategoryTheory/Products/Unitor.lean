/-
Copyright (c) 2024 Shanghe Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanghe Chen
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The left/right unitor equivalences `1 × C ≌ C` and `C × 1 ≌ C`.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CategoryTheory.prod

open scoped CategoryTheory.Prod

variable (C : Type u) [Category.{v} C]

/-- The left unitor functor `1 × C ⥤ C` -/
@[simps]
/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: : Discrete (PUnit : Type w) × C ⥤ C where
  body: X.2
  map f := f.2

中文:
定义 leftUnitor
  签名: : Discrete (PUnit : Type w) × C ⥤ C where
  定义体: X.2
  map f := f.2
-/
def leftUnitor : Discrete (PUnit : Type w) × C ⥤ C where
  obj X := X.2
  map f := f.2

/-- The right unitor functor `C × 1 ⥤ C` -/
@[simps]
/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: : C × Discrete (PUnit : Type w) ⥤ C where
  body: X.1
  map f := f.1

中文:
定义 rightUnitor
  签名: : C × Discrete (PUnit : Type w) ⥤ C where
  定义体: X.1
  map f := f.1
-/
def rightUnitor : C × Discrete (PUnit : Type w) ⥤ C where
  obj X := X.1
  map f := f.1

/-- The left inverse unitor `C ⥤ 1 × C` -/
@[simps]
/--
Definition of `leftInverseUnitor` / `leftInverseUnitor` 的定义

English:
definition leftInverseUnitor
  signature: : C ⥤ Discrete (PUnit : Type w) × C where
  body: ⟨⟨PUnit.unit⟩, X⟩
  map f := 𝟙 _ ×ₘ f

中文:
定义 leftInverseUnitor
  签名: : C ⥤ Discrete (PUnit : Type w) × C where
  定义体: ⟨⟨PUnit.unit⟩, X⟩
  map f := 𝟙 _ ×ₘ f

Depends on / 依赖: PUnit.unit
-/
def leftInverseUnitor : C ⥤ Discrete (PUnit : Type w) × C where
  obj X := ⟨⟨PUnit.unit⟩, X⟩
  map f := 𝟙 _ ×ₘ f

/-- The right inverse unitor `C ⥤ C × 1` -/
@[simps]
/--
Definition of `rightInverseUnitor` / `rightInverseUnitor` 的定义

English:
definition rightInverseUnitor
  signature: : C ⥤ C × Discrete (PUnit : Type w) where
  body: ⟨X, ⟨PUnit.unit⟩⟩
  map f := f ×ₘ 𝟙 _

中文:
定义 rightInverseUnitor
  签名: : C ⥤ C × Discrete (PUnit : Type w) where
  定义体: ⟨X, ⟨PUnit.unit⟩⟩
  map f := f ×ₘ 𝟙 _

Depends on / 依赖: PUnit.unit
-/
def rightInverseUnitor : C ⥤ C × Discrete (PUnit : Type w) where
  obj X := ⟨X, ⟨PUnit.unit⟩⟩
  map f := f ×ₘ 𝟙 _

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories expressing left unity of products of categories. -/
@[simps]
/--
Definition of `leftUnitorEquivalence` / `leftUnitorEquivalence` 的定义

English:
definition leftUnitorEquivalence
  signature: : Discrete (PUnit : Type w) × C ≌ C where
  body: leftUnitor C
  inverse := leftInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 leftUnitorEquivalence
  签名: : Discrete (PUnit : Type w) × C ≌ C where
  定义体: leftUnitor C
  inverse := leftInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: leftUnitor
-/
def leftUnitorEquivalence : Discrete (PUnit : Type w) × C ≌ C where
  functor := leftUnitor C
  inverse := leftInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories expressing right unity of products of categories. -/
@[simps]
/--
Definition of `rightUnitorEquivalence` / `rightUnitorEquivalence` 的定义

English:
definition rightUnitorEquivalence
  signature: : C × Discrete (PUnit : Type w) ≌ C where
  body: rightUnitor C
  inverse := rightInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 rightUnitorEquivalence
  签名: : C × Discrete (PUnit : Type w) ≌ C where
  定义体: rightUnitor C
  inverse := rightInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: rightUnitor
-/
def rightUnitorEquivalence : C × Discrete (PUnit : Type w) ≌ C where
  functor := rightUnitor C
  inverse := rightInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/--
Instance `leftUnitor_isEquivalence` / 实例 `leftUnitor_isEquivalence`

English:
instance leftUnitor_isEquivalence
  signature: : (leftUnitor C).IsEquivalence
  body: (leftUnitorEquivalence C).isEquivalence_functor

中文:
实例 leftUnitor_isEquivalence
  签名: : (leftUnitor C).IsEquivalence
  定义体: (leftUnitorEquivalence C).isEquivalence_functor

Depends on / 依赖: isEquivalence_functor, leftUnitorEquivalence
-/
instance leftUnitor_isEquivalence : (leftUnitor C).IsEquivalence :=
  (leftUnitorEquivalence C).isEquivalence_functor

/--
Instance `rightUnitor_isEquivalence` / 实例 `rightUnitor_isEquivalence`

English:
instance rightUnitor_isEquivalence
  signature: : (rightUnitor C).IsEquivalence
  body: (rightUnitorEquivalence C).isEquivalence_functor

中文:
实例 rightUnitor_isEquivalence
  签名: : (rightUnitor C).IsEquivalence
  定义体: (rightUnitorEquivalence C).isEquivalence_functor

Depends on / 依赖: isEquivalence_functor, rightUnitorEquivalence
-/
instance rightUnitor_isEquivalence : (rightUnitor C).IsEquivalence :=
  (rightUnitorEquivalence C).isEquivalence_functor

end CategoryTheory.prod
