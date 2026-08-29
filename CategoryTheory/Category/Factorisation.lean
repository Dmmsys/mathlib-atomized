/-
Copyright (c) 2023 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The Factorisation Category of a Category

`Factorisation f` is the category containing as objects all factorisations of a morphism `f`.

We show that `Factorisation f` always has an initial and a terminal object.

TODO: Show that `Factorisation f` is isomorphic to a comma category in two ways.

TODO: Make `MonoFactorisation f` a special case of a `Factorisation f`.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `Factorisation` / `Factorisation` 的定义

English:
structure Factorisation
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (4):
    - mid : C
    - ι : X ⟶ mid
    - π : mid ⟶ Y
    - ι_π : ι ≫ π = f  [default: by cat_disch]

中文:
结构 分解
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (4 个):
    - mid : C
    - ι : X ⟶ mid
    - π : mid ⟶ Y
    - ι_π : ι ≫ π = f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Factorisation {X Y : C} (f : X ⟶ Y) where
  /-- The midpoint of the factorisation. -/
  mid : C
  /-- The morphism into the factorisation midpoint. -/
  ι : X ⟶ mid
  /-- The morphism out of the factorisation midpoint. -/
  π : mid ⟶ Y
  /-- The factorisation condition. -/
  ι_π : ι ≫ π = f := by cat_disch

attribute [reassoc (attr := simp)] Factorisation.ι_π

namespace Factorisation

variable {X Y : C} {f : X ⟶ Y}

/-- Morphisms of `Factorisation f` consist of morphism between their midpoints and the obvious
commutativity conditions. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (d e : Factorisation f)
  axioms and operations (3):
    - h : d.mid ⟶ e.mid
    - ι_h : d.ι ≫ h = e.ι  [default: by cat_disch]
    - h_π : h ≫ e.π = d.π  [default: by cat_disch]

中文:
结构 态射
  参数: (d e : 分解 f)
  公理与运算 (3 个):
    - h : d.mid ⟶ e.mid
    - ι_h : d.ι ≫ h = e.ι  [默认: by cat_disch]
    - h_π : h ≫ e.π = d.π  [默认: by cat_disch]

Depends on / 依赖: Category, Category.assoc, Functor, Functor.flip_map_app, Iso.app_hom, Iso.trans_hom, app_hom, colimitHomIsoLimitYoneda, coyonedaOpColimitIsoLimitCoyoneda, flip_map_app, trans_hom
-/
protected structure Hom (d e : Factorisation f) : Type (max u v) where
  /-- The morphism between the midpoints of the factorizations. -/
  h : d.mid ⟶ e.mid
  /-- The left commuting triangle of the factorization morphism. -/
  ι_h : d.ι ≫ h = e.ι := by cat_disch
  /-- The right commuting triangle of the factorization morphism. -/
  h_π : h ≫ e.π = d.π := by cat_disch

attribute [reassoc (attr := simp)] Factorisation.Hom.ι_h Factorisation.Hom.h_π

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Quiver (Factorisation f)
  body: Factorisation.Hom d e

@[simps]

中文:
实例 :
  签名: 箭图 (分解 f)
  定义体: Factorisation.Hom d e

@[simps]

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Factorisation, Factorisation.Hom, Iso.inv_hom_id, colimitHomIsoLimitYoneda, id_comp, inv_hom_id
-/
instance : Quiver (Factorisation f) where
  Hom d e := Factorisation.Hom d e

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category.{max u v} (Factorisation f)
  body: { h := 𝟙 _ }
  comp f g := { h := f.h ≫ g.h }

中文:
实例 :
  签名: 范畴.{最大值 u v} (分解 f)
  定义体: { h := 𝟙 _ }
  comp f g := { h := f.h ≫ g.h }
-/
instance : Category.{max u v} (Factorisation f) where
  id d := { h := 𝟙 _ }
  comp f g := { h := f.h ≫ g.h }

attribute [reassoc] comp_h

variable (d : Factorisation f)

/-- The initial object in `Factorisation f`, with the domain of `f` as its midpoint. -/
@[simps]
/--
Definition of `initial` / `initial` 的定义

English:
definition initial
  signature: : Factorisation f where
  body: X
  ι := 𝟙 _
  π := f

中文:
定义 initial
  签名: : 分解 f where
  定义体: X
  ι := 𝟙 _
  π := f
-/
protected def initial : Factorisation f where
  mid := X
  ι := 𝟙 _
  π := f

set_option backward.defeqAttrib.useBackward true in
/-- The unique morphism out of `Factorisation.initial f`. -/
@[simps]
/--
Definition of `initialHom` / `initialHom` 的定义

English:
definition initialHom
  signature: (d : Factorisation f)
  body: d.ι

中文:
定义 initialHom
  签名: (d : 分解 f)
  定义体: d.ι
-/
protected def initialHom (d : Factorisation f) :
    Factorisation.Hom (Factorisation.initial : Factorisation f) d where
  h := d.ι

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique ((Factorisation.initial : Factorisation f) ⟶ d)
  body: Factorisation.initialHom d
  uniq f := by apply Factorisation.Hom.ext; simp [← f.ι_h]

中文:
实例 :
  签名: 唯一 ((分解.initial : 分解 f) ⟶ d)
  定义体: Factorisation.initialHom d
  uniq f := by apply Factorisation.Hom.ext; simp [← f.ι_h]

Depends on / 依赖: Factorisation, Factorisation.initialHom, initialHom
-/
instance : Unique ((Factorisation.initial : Factorisation f) ⟶ d) where
  default := Factorisation.initialHom d
  uniq f := by apply Factorisation.Hom.ext; simp [← f.ι_h]

/-- The terminal object in `Factorisation f`, with the codomain of `f` as its midpoint. -/
@[simps]
/--
Definition of `terminal` / `terminal` 的定义

English:
definition terminal
  signature: : Factorisation f where
  body: Y
  ι := f
  π := 𝟙 _

中文:
定义 terminal
  签名: : 分解 f where
  定义体: Y
  ι := f
  π := 𝟙 _
-/
protected def terminal : Factorisation f where
  mid := Y
  ι := f
  π := 𝟙 _

set_option backward.defeqAttrib.useBackward true in
/-- The unique morphism into `Factorisation.terminal f`. -/
@[simps]
/--
Definition of `terminalHom` / `terminalHom` 的定义

English:
definition terminalHom
  signature: (d : Factorisation f)
  body: d.π

中文:
定义 terminalHom
  签名: (d : 分解 f)
  定义体: d.π
-/
protected def terminalHom (d : Factorisation f) :
    Factorisation.Hom d (Factorisation.terminal : Factorisation f) where
  h := d.π

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (d ⟶ (Factorisation.terminal : Factorisation f))
  body: Factorisation.terminalHom d
  uniq f := by apply Factorisation.Hom.ext; simp [← f.h_π]

中文:
实例 :
  签名: 唯一 (d ⟶ (分解.terminal : 分解 f))
  定义体: Factorisation.terminalHom d
  uniq f := by apply Factorisation.Hom.ext; simp [← f.h_π]

Depends on / 依赖: Factorisation, Factorisation.terminalHom, terminalHom
-/
instance : Unique (d ⟶ (Factorisation.terminal : Factorisation f)) where
  default := Factorisation.terminalHom d
  uniq f := by apply Factorisation.Hom.ext; simp [← f.h_π]

open Limits

/--
Definition of `IsInitial_initial` / `IsInitial_initial` 的定义

English:
definition IsInitial_initial
  signature: : IsInitial (Factorisation.initial : Factorisation f)
  body: IsInitial.ofUnique _

中文:
定义 IsInitial_initial
  签名: : IsInitial (分解.initial : 分解 f)
  定义体: IsInitial.ofUnique _

Depends on / 依赖: IsInitial, IsInitial.ofUnique, ofUnique
-/
def IsInitial_initial : IsInitial (Factorisation.initial : Factorisation f) := IsInitial.ofUnique _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasInitial (Factorisation f)
  body: Limits.hasInitial_of_unique Factorisation.initial

中文:
实例 :
  签名: HasInitial (分解 f)
  定义体: Limits.hasInitial_of_unique Factorisation.initial

Depends on / 依赖: Factorisation, Factorisation.initial, Limits, Limits.hasInitial_of_unique, hasInitial_of_unique, initial
-/
instance : HasInitial (Factorisation f) := Limits.hasInitial_of_unique Factorisation.initial

/--
Definition of `IsTerminal_terminal` / `IsTerminal_terminal` 的定义

English:
definition IsTerminal_terminal
  signature: : IsTerminal (Factorisation.terminal : Factorisation f)
  body: IsTerminal.ofUnique _

中文:
定义 IsTerminal_terminal
  签名: : 是终止 (分解.terminal : 分解 f)
  定义体: IsTerminal.ofUnique _

Depends on / 依赖: Category, Category.assoc, HasLimit, HasLimit.isoOfNatIso_hom_, IsTerminal, IsTerminal.ofUnique, Iso.trans_hom, colimitCoyonedaHomIsoLimit, colimitHomIsoLimitYoneda, coyonedaLemma, ofUnique, trans_hom, uliftFunctor
-/
def IsTerminal_terminal : IsTerminal (Factorisation.terminal : Factorisation f) :=
IsTerminal.ofUnique _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasTerminal (Factorisation f)
  body: Limits.hasTerminal_of_unique Factorisation.terminal

中文:
实例 :
  签名: 有终止 (分解 f)
  定义体: Limits.hasTerminal_of_unique Factorisation.terminal

Depends on / 依赖: Factorisation, Factorisation.terminal, Limits, Limits.hasTerminal_of_unique, hasTerminal_of_unique, terminal
-/
instance : HasTerminal (Factorisation f) := Limits.hasTerminal_of_unique Factorisation.terminal

/-- The forgetful functor from `Factorisation f` to the underlying category `C`. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Factorisation f ⥤ C where
  body: Factorisation.mid
  map f := f.h

中文:
定义 forget
  签名: : 分解 f ⥤ C where
  定义体: Factorisation.mid
  map f := f.h

Depends on / 依赖: Factorisation, Factorisation.mid
-/
def forget : Factorisation f ⥤ C where
  obj := Factorisation.mid
  map f := f.h

end Factorisation

end CategoryTheory
