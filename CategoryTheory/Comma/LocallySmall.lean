/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Comma categories are locally small

We introduce instances showing that the various comma categories
are locally small when the relevant categories that are
involved are locally small.

-/

public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} T]

/--
Instance `Comma.locallySmall` / 实例 `Comma.locallySmall`

English:
instance Comma.locallySmall
  body: small_of_injective.{w}
      (f := fun g => (⟨g.left, g.right⟩ : _ × _))
        (fun _ _ _ => by aesop)

中文:
实例 Comma.locallySmall
  定义体: small_of_injective.{w}
      (f := fun g => (⟨g.left, g.right⟩ : _ × _))
        (fun _ _ _ => by aesop)

Depends on / 依赖: small_of_injective
-/
instance Comma.locallySmall
    (L : A ⥤ T) (R : B ⥤ T) [LocallySmall.{w} A] [LocallySmall.{w} B] :
    LocallySmall.{w} (Comma L R) where
  hom_small X Y := small_of_injective.{w}
      (f := fun g => (⟨g.left, g.right⟩ : _ × _))
        (fun _ _ _ => by aesop)

/--
Instance `StructuredArrow.locallySmall` / 实例 `StructuredArrow.locallySmall`

English:
instance StructuredArrow.locallySmall
  signature: (S : T) (T : B ⥤ T)
  body: Comma.locallySmall _ _

中文:
实例 StructuredArrow.locallySmall
  签名: (S : T) (T : B ⥤ T)
  定义体: Comma.locallySmall _ _

Depends on / 依赖: Comma.locallySmall, locallySmall
-/
instance StructuredArrow.locallySmall (S : T) (T : B ⥤ T)
    [LocallySmall.{w} B] :
    LocallySmall.{w} (StructuredArrow S T) :=
  Comma.locallySmall _ _

/--
Instance `CostructuredArrow.locallySmall` / 实例 `CostructuredArrow.locallySmall`

English:
instance CostructuredArrow.locallySmall
  signature: (S : A ⥤ T) (X : T)
  body: Comma.locallySmall _ _

中文:
实例 CostructuredArrow.locallySmall
  签名: (S : A ⥤ T) (X : T)
  定义体: Comma.locallySmall _ _

Depends on / 依赖: Comma.locallySmall, locallySmall
-/
instance CostructuredArrow.locallySmall (S : A ⥤ T) (X : T)
    [LocallySmall.{w} A] :
    LocallySmall.{w} (CostructuredArrow S X) :=
  Comma.locallySmall _ _

/--
Instance `Over.locallySmall` / 实例 `Over.locallySmall`

English:
instance Over.locallySmall
  signature: (X : T) [LocallySmall.{w} T]
  body: CostructuredArrow.locallySmall _ _

中文:
实例 Over.locallySmall
  签名: (X : T) [LocallySmall.{w} T]
  定义体: CostructuredArrow.locallySmall _ _

Depends on / 依赖: CostructuredArrow, CostructuredArrow.locallySmall, locallySmall
-/
instance Over.locallySmall (X : T) [LocallySmall.{w} T] :
    LocallySmall.{w} (Over X) :=
  CostructuredArrow.locallySmall _ _

/--
Instance `Under.locallySmall` / 实例 `Under.locallySmall`

English:
instance Under.locallySmall
  signature: (X : T) [LocallySmall.{w} T]
  body: StructuredArrow.locallySmall _ _

中文:
实例 Under.locallySmall
  签名: (X : T) [LocallySmall.{w} T]
  定义体: StructuredArrow.locallySmall _ _

Depends on / 依赖: StructuredArrow, StructuredArrow.locallySmall, locallySmall
-/
instance Under.locallySmall (X : T) [LocallySmall.{w} T] :
    LocallySmall.{w} (Under X) :=
  StructuredArrow.locallySmall _ _

end CategoryTheory
