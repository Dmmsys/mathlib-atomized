/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate

/-! # Morphism properties equipped with a localized category

If `C : Type u` is a category (with `[Category.{v} C]`), and
`W : MorphismProperty C`, then the constructed localized
category `W.Localization` is in `Type u` (the objects are
essentially the same as those of `C`), but the morphisms
are in `Type (max u v)`. In particular situations, it
may happen that there is a localized category for `W`
whose morphisms are in a lower universe like `v`: it shall
be so for the homotopy categories of model categories (TODO),
and it should also be so for the derived categories of
Grothendieck abelian categories (TODO: but this will be
very technical).

Then, in order to allow the user to provide a localized
category with specific universe parameters when it exists,
we introduce a typeclass `MorphismProperty.HasLocalization.{w} W`
which contains the data of a localized category `D` for `W`
with `D : Type u` and `[Category.{w} D]`. Then, all
definitions which involve "the" localized category
for `W` should contain a `[MorphismProperty.HasLocalization.{w} W]`
assumption for a suitable `w`. The functor `W.Q' : C ⥤ W.Localization'`
shall be the localization functor for this fixed choice of the
localized category. If the statement of a theorem does not
involve the localized category, but the proof does,
it is no longer necessary to use a `HasLocalization`
assumption, but one may use
`HasLocalization.standard` in the proof instead.

-/

@[expose] public noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C)

namespace MorphismProperty

/--
Definition of `HasLocalization` / `HasLocalization` 的定义

English:
class HasLocalization
  parameters: where
  axioms and operations (4):
    - {D : Type u}
    - [hD : Category.{w} D]
    - L : C ⥤ D
    - [hL : L.IsLocalization W]

中文:
类 有Localization
  参数: where
  公理与运算 (4 个):
    - {D : 类型u}
    - [hD : 范畴.{w} D]
    - L : C ⥤ D
    - [hL : L.是Localization W]
-/
class HasLocalization where
  /-- the objects of the localized category. -/
  {D : Type u}
  /-- the category structure. -/
  [hD : Category.{w} D]
  /-- the localization functor. -/
  L : C ⥤ D
  [hL : L.IsLocalization W]

variable [HasLocalization.{w} W]

/--
Definition of `Localization'` / `Localization'` 的定义

English:
definition Localization'
  body: HasLocalization.D W

中文:
定义 Localization'
  定义体: HasLocalization.D W

Depends on / 依赖: HasLocalization, HasLocalization.D, Iso.inv, NatTrans, NatTrans.congr_app, _zero_add, congr_app, congr_arg, shiftFunctorAdd
-/
def Localization' := HasLocalization.D W

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category W.Localization'
  body: HasLocalization.hD

中文:
实例 :
  签名: 范畴 W.Localization'
  定义体: HasLocalization.hD

Depends on / 依赖: HasLocalization, HasLocalization.hD
-/
instance : Category W.Localization' := HasLocalization.hD

/--
Definition of `Q'` / `Q'` 的定义

English:
definition Q'
  signature: : C ⥤ W.Localization'
  body: HasLocalization.L

中文:
定义 Q'
  签名: : C ⥤ W.Localization'
  定义体: HasLocalization.L

Depends on / 依赖: HasLocalization, HasLocalization.L, Iso.hom, NatTrans, NatTrans.congr_app, _add_zero, congr_app, congr_arg, shiftFunctorAdd
-/
def Q' : C ⥤ W.Localization' := HasLocalization.L

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: W.Q'.IsLocalization W
  body: HasLocalization.hL

中文:
实例 :
  签名: W.Q'.是Localization W
  定义体: HasLocalization.hL

Depends on / 依赖: HasLocalization, HasLocalization.hL
-/
instance : W.Q'.IsLocalization W := HasLocalization.hL

/-- The constructed localized category. -/
@[instance_reducible]
/--
Definition of `HasLocalization.standard` / `HasLocalization.standard` 的定义

English:
definition HasLocalization.standard
  signature: : HasLocalization.{max u v} W where
  body: W.Q

中文:
定义 有Localization.standard
  签名: : 有Localization.{最大值 u v} W where
  定义体: W.Q

Depends on / 依赖: Iso.inv, NatTrans, NatTrans.congr_app, _add_zero, congr_app, congr_arg, shiftFunctorAdd
-/
def HasLocalization.standard : HasLocalization.{max u v} W where
  L := W.Q

end MorphismProperty

end CategoryTheory
