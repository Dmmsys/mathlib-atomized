/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta, Daniel Carranza, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.Tactic.BDSimp

/-!
# Closed monoidal categories

Define (right) closed objects and (right) closed monoidal categories.

## TODO
Some theorems about Cartesian closed categories
should be generalised and moved to this file.
-/

@[expose] public section


universe v u u₂ v₂

namespace CategoryTheory

open Category MonoidalCategory

-- Note that this class carries a particular choice of right adjoint,
-- (which is only unique up to isomorphism),
-- not merely the existence of such, and
-- so definitional properties of instances may be important.
/--
Definition of `Closed` / `Closed` 的定义

English:
class Closed
  parameters: {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (X : C)
  axioms and operations (2):
    - rightAdj : C ⥤ C
    - adj : tensorLeft X ⊣ rightAdj

中文:
类 Closed
  参数: {C : 类型u} [Category.{v} C] [MonoidalCategory.{v} C] (X : C)
  公理与运算 (2 个):
    - rightAdj : C ⥤ C
    - adj : tensorLeft X ⊣ rightAdj
-/
class Closed {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (X : C) where
  /-- a choice of a right adjoint for `tensorLeft X` -/
  rightAdj : C ⥤ C
  /-- `tensorLeft X` is a left adjoint -/
  adj : tensorLeft X ⊣ rightAdj

/--
Definition of `MonoidalClosed` / `MonoidalClosed` 的定义

English:
class MonoidalClosed
  parameters: (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
  axioms and operations (1):
    - closed((X : C)) : Closed X  [default: by infer_instance]

中文:
类 MonoidalClosed
  参数: (C : 类型u) [Category.{v} C] [MonoidalCategory.{v} C]
  公理与运算 (1 个):
    - closed((X : C)) : Closed X  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class MonoidalClosed (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  closed (X : C) : Closed X := by infer_instance

attribute [instance_reducible, instance 100] MonoidalClosed.closed

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- If `X` and `Y` are closed then `X ⊗ Y` is.
This isn't an instance because it's not usually how we want to construct internal homs,
we'll usually prove all objects are closed uniformly.
-/
@[instance_reducible]
/--
Definition of `tensorClosed` / `tensorClosed` 的定义

English:
definition tensorClosed
  signature: {X Y : C} (hX : Closed X) (hY : Closed Y)
  body: Closed.rightAdj X ⋙ Closed.rightAdj Y
  adj := (hY.adj.comp hX.adj).ofNatIsoLeft (MonoidalCategory.tensorLeftTensor X Y).symm

中文:
定义 tensorClosed
  签名: {X Y : C} (hX : Closed X) (hY : Closed Y)
  定义体: Closed.rightAdj X ⋙ Closed.rightAdj Y
  adj := (hY.adj.comp hX.adj).ofNatIsoLeft (MonoidalCategory.tensorLeftTensor X Y).symm

Depends on / 依赖: Closed, Closed.rightAdj, rightAdj
-/
def tensorClosed {X Y : C} (hX : Closed X) (hY : Closed Y) : Closed (X otimes Y) where
  rightAdj := Closed.rightAdj X ⋙ Closed.rightAdj Y
  adj := (hY.adj.comp hX.adj).ofNatIsoLeft (MonoidalCategory.tensorLeftTensor X Y).symm

/-- The unit object is always closed.
This isn't an instance because most of the time we'll prove closedness for all objects at once,
rather than just for this one.
-/
@[instance_reducible]
/--
Definition of `unitClosed` / `unitClosed` 的定义

English:
definition unitClosed
  signature: : Closed (𝟙_ C) where
  body: 𝟭 C
  adj := Adjunction.id.ofNatIsoLeft (MonoidalCategory.leftUnitorNatIso C).symm

中文:
定义 unitClosed
  签名: : Closed (𝟙_ C) where
  定义体: 𝟭 C
  adj := Adjunction.id.ofNatIsoLeft (MonoidalCategory.leftUnitorNatIso C).symm
-/
def unitClosed : Closed (𝟙_ C) where
  rightAdj := 𝟭 C
  adj := Adjunction.id.ofNatIsoLeft (MonoidalCategory.leftUnitorNatIso C).symm

variable (A B : C) {X X' Y Y' Z : C}
variable [Closed A]

/--
Definition of `ihom` / `ihom` 的定义

English:
definition ihom
  signature: : C ⥤ C
  body: Closed.rightAdj (X := A)

中文:
定义 ihom
  签名: : C ⥤ C
  定义体: Closed.rightAdj (X := A)

Depends on / 依赖: Closed, Closed.rightAdj, rightAdj
-/
def ihom : C ⥤ C :=
  Closed.rightAdj (X := A)

namespace ihom

/--
Definition of `adjunction` / `adjunction` 的定义

English:
definition adjunction
  signature: : tensorLeft A ⊣ ihom A
  body: Closed.adj

中文:
定义 adjunction
  签名: : tensorLeft A ⊣ ihom A
  定义体: Closed.adj

Depends on / 依赖: Closed, Closed.adj
-/
def adjunction : tensorLeft A ⊣ ihom A :=
  Closed.adj

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (tensorLeft A).IsLeftAdjoint
  body: (ihom.adjunction A).isLeftAdjoint

中文:
实例 :
  签名: (tensorLeft A).IsLeftAdjoint
  定义体: (ihom.adjunction A).isLeftAdjoint

Depends on / 依赖: adjunction, ihom.adjunction, isLeftAdjoint
-/
instance : (tensorLeft A).IsLeftAdjoint :=
  (ihom.adjunction A).isLeftAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ihom A).IsRightAdjoint
  body: (ihom.adjunction A).isRightAdjoint

中文:
实例 :
  签名: (ihom A).IsRightAdjoint
  定义体: (ihom.adjunction A).isRightAdjoint

Depends on / 依赖: adjunction, ihom.adjunction, isRightAdjoint
-/
instance : (ihom A).IsRightAdjoint :=
  (ihom.adjunction A).isRightAdjoint

/--
Definition of `ev` / `ev` 的定义

English:
definition ev
  signature: : ihom A ⋙ tensorLeft A ⟶ 𝟭 C
  body: (ihom.adjunction A).counit

中文:
定义 ev
  签名: : ihom A ⋙ tensorLeft A ⟶ 𝟭 C
  定义体: (ihom.adjunction A).counit

Depends on / 依赖: adjunction, counit, ihom.adjunction
-/
def ev : ihom A ⋙ tensorLeft A ⟶ 𝟭 C :=
  (ihom.adjunction A).counit

/--
Definition of `coev` / `coev` 的定义

English:
definition coev
  signature: : 𝟭 C ⟶ tensorLeft A ⋙ ihom A
  body: (ihom.adjunction A).unit

@[simp]

中文:
定义 coev
  签名: : 𝟭 C ⟶ tensorLeft A ⋙ ihom A
  定义体: (ihom.adjunction A).unit

@[simp]

Depends on / 依赖: adjunction, ihom.adjunction
-/
def coev : 𝟭 C ⟶ tensorLeft A ⋙ ihom A :=
  (ihom.adjunction A).unit

@[simp]
/--
theorem `ihom_adjunction_counit` / 定理 `ihom_adjunction_counit`

English:
theorem ihom_adjunction_counit
  statement: (ihom.adjunction A).counit = ev A
  proof: rfl

@[simp]

中文:
定理 ihom_adjunction_counit
  结论: (ihom.adjunction A).counit = ev A
  证明: rfl

@[simp]
-/
theorem ihom_adjunction_counit : (ihom.adjunction A).counit = ev A :=
  rfl

@[simp]
/--
theorem `ihom_adjunction_unit` / 定理 `ihom_adjunction_unit`

English:
theorem ihom_adjunction_unit
  statement: (ihom.adjunction A).unit = coev A
  proof: rfl

中文:
定理 ihom_adjunction_unit
  结论: (ihom.adjunction A).unit = coev A
  证明: rfl
-/
theorem ihom_adjunction_unit : (ihom.adjunction A).unit = coev A :=
  rfl

set_option backward.isDefEq.respectTransparency false in -- Needed in DayConvolution/Closed.lean
@[reassoc (attr := simp)]
/--
theorem `ev_naturality` / 定理 `ev_naturality`

English:
theorem ev_naturality
  given: {X Y : C} (f : X ⟶ Y)
  proof: (ev A).naturality f

#adaptation_note

中文:
定理 ev_naturality
  条件: {X Y : C} (f : X ⟶ Y)
  证明: (ev A).naturality f

#adaptation_note

Depends on / 依赖: naturality
-/
theorem ev_naturality {X Y : C} (f : X ⟶ Y) :
    A ◁ (ihom A).map f ≫ (ev A).app Y = (ev A).app X ≫ f :=
  (ev A).naturality f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `coev_naturality` / 定理 `coev_naturality`

English:
theorem coev_naturality
  given: {X Y : C} (f : X ⟶ Y)
  proof: (coev A).naturality f

中文:
定理 coev_naturality
  条件: {X Y : C} (f : X ⟶ Y)
  证明: (coev A).naturality f

Depends on / 依赖: naturality
-/
theorem coev_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (coev A).app Y = (coev A).app X ≫ (ihom A).map (A ◁ f) :=
  (coev A).naturality f

set_option quotPrecheck false in
/-- `A ⟶[C] B` denotes the internal hom from `A` to `B` -/
notation A " ⟶[" C "] " B:10 => (@ihom C _ _ A _).obj B

@[reassoc (attr := simp)]
/--
theorem `ev_coev` / 定理 `ev_coev`

English:
theorem ev_coev
  statement: (A ◁ (coev A).app B) ≫ (ev A).app (A otimes B) = 𝟙 (A otimes B)
  proof: (ihom.adjunction A).left_triangle_components _

@[reassoc (attr := simp)]

中文:
定理 ev_coev
  结论: (A ◁ (coev A).app B) ≫ (ev A).app (A otimes B) = 𝟙 (A otimes B)
  证明: (ihom.adjunction A).left_triangle_components _

@[reassoc (attr := simp)]

Depends on / 依赖: adjunction, ihom.adjunction, left_triangle_components
-/
theorem ev_coev : (A ◁ (coev A).app B) ≫ (ev A).app (A otimes B) = 𝟙 (A otimes B) :=
  (ihom.adjunction A).left_triangle_components _

@[reassoc (attr := simp)]
/--
theorem `coev_ev` / 定理 `coev_ev`

English:
theorem coev_ev
  statement: (coev A).app (A ⟶[C] B) ≫ (ihom A).map ((ev A).app B) = 𝟙 (A ⟶[C] B)
  proof: Adjunction.right_triangle_components (ihom.adjunction A) _

中文:
定理 coev_ev
  结论: (coev A).app (A ⟶[C] B) ≫ (ihom A).map ((ev A).app B) = 𝟙 (A ⟶[C] B)
  证明: Adjunction.right_triangle_components (ihom.adjunction A) _

Depends on / 依赖: Adjunction, Adjunction.right_triangle_components, adjunction, ihom.adjunction, right_triangle_components
-/
theorem coev_ev : (coev A).app (A ⟶[C] B) ≫ (ihom A).map ((ev A).app B) = 𝟙 (A ⟶[C] B) :=
  Adjunction.right_triangle_components (ihom.adjunction A) _

end ihom

open CategoryTheory.Limits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimits (tensorLeft A)
  body: (ihom.adjunction A).leftAdjoint_preservesColimits

中文:
实例 :
  签名: PreservesColimits (tensorLeft A)
  定义体: (ihom.adjunction A).leftAdjoint_preservesColimits

Depends on / 依赖: adjunction, ihom.adjunction, leftAdjoint_preservesColimits
-/
instance : PreservesColimits (tensorLeft A) :=
  (ihom.adjunction A).leftAdjoint_preservesColimits

variable {A}

-- Wrap these in a namespace so we don't clash with the core versions.
namespace MonoidalClosed

/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: : (A otimes Y ⟶ X) -> (Y ⟶ A ⟶[C] X)
  body: (ihom.adjunction A).homEquiv _ _

中文:
定义 curry
  签名: : (A otimes Y ⟶ X) -> (Y ⟶ A ⟶[C] X)
  定义体: (ihom.adjunction A).homEquiv _ _

Depends on / 依赖: adjunction, homEquiv, ihom.adjunction
-/
def curry : (A otimes Y ⟶ X) -> (Y ⟶ A ⟶[C] X) :=
  (ihom.adjunction A).homEquiv _ _

/--
Definition of `uncurry` / `uncurry` 的定义

English:
definition uncurry
  signature: : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X)
  body: ((ihom.adjunction A).homEquiv _ _).symm

中文:
定义 uncurry
  签名: : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X)
  定义体: ((ihom.adjunction A).homEquiv _ _).symm

Depends on / 依赖: adjunction, homEquiv, ihom.adjunction
-/
def uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X) :=
  ((ihom.adjunction A).homEquiv _ _).symm

/--
theorem `homEquiv_apply_eq` / 定理 `homEquiv_apply_eq`

English:
theorem homEquiv_apply_eq
  given: (f : A otimes Y ⟶ X)
  statement: (ihom.adjunction A).homEquiv _ _ f = curry f
  proof: rfl

中文:
定理 homEquiv_apply_eq
  条件: (f : A otimes Y ⟶ X)
  结论: (ihom.adjunction A).homEquiv _ _ f = curry f
  证明: rfl
-/
theorem homEquiv_apply_eq (f : A otimes Y ⟶ X) : (ihom.adjunction A).homEquiv _ _ f = curry f :=
  rfl

/--
theorem `homEquiv_symm_apply_eq` / 定理 `homEquiv_symm_apply_eq`

English:
theorem homEquiv_symm_apply_eq
  given: (f : Y ⟶ A ⟶[C] X)
  proof: rfl

@[reassoc]

中文:
定理 homEquiv_symm_apply_eq
  条件: (f : Y ⟶ A ⟶[C] X)
  证明: rfl

@[reassoc]
-/
theorem homEquiv_symm_apply_eq (f : Y ⟶ A ⟶[C] X) :
    ((ihom.adjunction A).homEquiv _ _).symm f = uncurry f :=
  rfl

@[reassoc]
/--
theorem `curry_natural_left` / 定理 `curry_natural_left`

English:
theorem curry_natural_left
  given: (f : X ⟶ X') (g : A otimes X' ⟶ Y)
  statement: curry (_ ◁ f ≫ g) = f ≫ curry g
  proof: Adjunction.homEquiv_naturality_left _ _ _

@[reassoc]

中文:
定理 curry_natural_left
  条件: (f : X ⟶ X') (g : A otimes X' ⟶ Y)
  结论: curry (_ ◁ f ≫ g) = f ≫ curry g
  证明: Adjunction.homEquiv_naturality_left _ _ _

@[reassoc]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_left, homEquiv_naturality_left
-/
theorem curry_natural_left (f : X ⟶ X') (g : A otimes X' ⟶ Y) : curry (_ ◁ f ≫ g) = f ≫ curry g :=
  Adjunction.homEquiv_naturality_left _ _ _

@[reassoc]
/--
theorem `curry_natural_right` / 定理 `curry_natural_right`

English:
theorem curry_natural_right
  given: (f : A otimes X ⟶ Y) (g : Y ⟶ Y')
  proof: Adjunction.homEquiv_naturality_right _ _ _

@[reassoc]

中文:
定理 curry_natural_right
  条件: (f : A otimes X ⟶ Y) (g : Y ⟶ Y')
  证明: Adjunction.homEquiv_naturality_right _ _ _

@[reassoc]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_right, homEquiv_naturality_right
-/
theorem curry_natural_right (f : A otimes X ⟶ Y) (g : Y ⟶ Y') :
    curry (f ≫ g) = curry f ≫ (ihom _).map g :=
  Adjunction.homEquiv_naturality_right _ _ _

@[reassoc]
/--
theorem `uncurry_natural_right` / 定理 `uncurry_natural_right`

English:
theorem uncurry_natural_right
  given: (f : X ⟶ A ⟶[C] Y) (g : Y ⟶ Y')
  proof: Adjunction.homEquiv_naturality_right_symm _ _ _

@[reassoc]

中文:
定理 uncurry_natural_right
  条件: (f : X ⟶ A ⟶[C] Y) (g : Y ⟶ Y')
  证明: Adjunction.homEquiv_naturality_right_symm _ _ _

@[reassoc]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_right_symm, homEquiv_naturality_right_symm
-/
theorem uncurry_natural_right (f : X ⟶ A ⟶[C] Y) (g : Y ⟶ Y') :
    uncurry (f ≫ (ihom _).map g) = uncurry f ≫ g :=
  Adjunction.homEquiv_naturality_right_symm _ _ _

@[reassoc]
/--
theorem `uncurry_natural_left` / 定理 `uncurry_natural_left`

English:
theorem uncurry_natural_left
  given: (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y)
  proof: Adjunction.homEquiv_naturality_left_symm _ _ _

@[simp]

中文:
定理 uncurry_natural_left
  条件: (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y)
  证明: Adjunction.homEquiv_naturality_left_symm _ _ _

@[simp]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_left_symm, homEquiv_naturality_left_symm
-/
theorem uncurry_natural_left (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) :
    uncurry (f ≫ g) = _ ◁ f ≫ uncurry g :=
  Adjunction.homEquiv_naturality_left_symm _ _ _

@[simp]
/--
theorem `uncurry_curry` / 定理 `uncurry_curry`

English:
theorem uncurry_curry
  given: (f : A otimes X ⟶ Y)
  statement: uncurry (curry f) = f
  proof: (Closed.adj.homEquiv _ _).left_inv f

@[simp]

中文:
定理 uncurry_curry
  条件: (f : A otimes X ⟶ Y)
  结论: uncurry (curry f) = f
  证明: (Closed.adj.homEquiv _ _).left_inv f

@[simp]

Depends on / 依赖: Closed, Closed.adj.homEquiv, homEquiv, left_inv
-/
theorem uncurry_curry (f : A otimes X ⟶ Y) : uncurry (curry f) = f :=
  (Closed.adj.homEquiv _ _).left_inv f

@[simp]
/--
theorem `curry_uncurry` / 定理 `curry_uncurry`

English:
theorem curry_uncurry
  given: (f : X ⟶ A ⟶[C] Y)
  statement: curry (uncurry f) = f
  proof: (Closed.adj.homEquiv _ _).right_inv f

中文:
定理 curry_uncurry
  条件: (f : X ⟶ A ⟶[C] Y)
  结论: curry (uncurry f) = f
  证明: (Closed.adj.homEquiv _ _).right_inv f

Depends on / 依赖: Closed, Closed.adj.homEquiv, homEquiv, right_inv
-/
theorem curry_uncurry (f : X ⟶ A ⟶[C] Y) : curry (uncurry f) = f :=
  (Closed.adj.homEquiv _ _).right_inv f

/--
theorem `curry_eq_iff` / 定理 `curry_eq_iff`

English:
theorem curry_eq_iff
  given: (f : A otimes Y ⟶ X) (g : Y ⟶ A ⟶[C] X)
  statement: curry f = g ↔ f = uncurry g
  proof: Adjunction.homEquiv_apply_eq (ihom.adjunction A) f g

中文:
定理 curry_eq_iff
  条件: (f : A otimes Y ⟶ X) (g : Y ⟶ A ⟶[C] X)
  结论: curry f = g ↔ f = uncurry g
  证明: Adjunction.homEquiv_apply_eq (ihom.adjunction A) f g

Depends on / 依赖: Adjunction, Adjunction.homEquiv_apply_eq, adjunction, homEquiv_apply_eq, ihom.adjunction
-/
theorem curry_eq_iff (f : A otimes Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : curry f = g ↔ f = uncurry g :=
  Adjunction.homEquiv_apply_eq (ihom.adjunction A) f g

/--
theorem `eq_curry_iff` / 定理 `eq_curry_iff`

English:
theorem eq_curry_iff
  given: (f : A otimes Y ⟶ X) (g : Y ⟶ A ⟶[C] X)
  statement: g = curry f ↔ uncurry g = f
  proof: Adjunction.eq_homEquiv_apply (ihom.adjunction A) f g

中文:
定理 eq_curry_iff
  条件: (f : A otimes Y ⟶ X) (g : Y ⟶ A ⟶[C] X)
  结论: g = curry f ↔ uncurry g = f
  证明: Adjunction.eq_homEquiv_apply (ihom.adjunction A) f g

Depends on / 依赖: Adjunction, Adjunction.eq_homEquiv_apply, adjunction, eq_homEquiv_apply, ihom.adjunction
-/
theorem eq_curry_iff (f : A otimes Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : g = curry f ↔ uncurry g = f :=
  Adjunction.eq_homEquiv_apply (ihom.adjunction A) f g

-- I don't think these two should be simp.
/--
theorem `uncurry_eq` / 定理 `uncurry_eq`

English:
theorem uncurry_eq
  given: (g : Y ⟶ A ⟶[C] X)
  statement: uncurry g = (A ◁ g) ≫ (ihom.ev A).app X
  proof: by
  rfl

中文:
定理 uncurry_eq
  条件: (g : Y ⟶ A ⟶[C] X)
  结论: uncurry g = (A ◁ g) ≫ (ihom.ev A).app X
  证明: by
  rfl
-/
theorem uncurry_eq (g : Y ⟶ A ⟶[C] X) : uncurry g = (A ◁ g) ≫ (ihom.ev A).app X := by
  rfl

/--
theorem `curry_eq` / 定理 `curry_eq`

English:
theorem curry_eq
  given: (g : A otimes Y ⟶ X)
  statement: curry g = (ihom.coev A).app Y ≫ (ihom A).map g
  proof: rfl

中文:
定理 curry_eq
  条件: (g : A otimes Y ⟶ X)
  结论: curry g = (ihom.coev A).app Y ≫ (ihom A).map g
  证明: rfl
-/
theorem curry_eq (g : A otimes Y ⟶ X) : curry g = (ihom.coev A).app Y ≫ (ihom A).map g :=
  rfl

/--
theorem `curry_injective` / 定理 `curry_injective`

English:
theorem curry_injective
  statement: Function.Injective (curry : (A otimes Y ⟶ X) -> (Y ⟶ A ⟶[C] X))
  proof: (Closed.adj.homEquiv _ _).injective

中文:
定理 curry_injective
  结论: Function.Injective (curry : (A otimes Y ⟶ X) -> (Y ⟶ A ⟶[C] X))
  证明: (Closed.adj.homEquiv _ _).injective

Depends on / 依赖: Closed, Closed.adj.homEquiv, homEquiv, injective
-/
theorem curry_injective : Function.Injective (curry : (A otimes Y ⟶ X) -> (Y ⟶ A ⟶[C] X)) :=
  (Closed.adj.homEquiv _ _).injective

/--
theorem `uncurry_injective` / 定理 `uncurry_injective`

English:
theorem uncurry_injective
  statement: Function.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X))
  proof: (Closed.adj.homEquiv _ _).symm.injective

中文:
定理 uncurry_injective
  结论: Function.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X))
  证明: (Closed.adj.homEquiv _ _).symm.injective

Depends on / 依赖: Closed, Closed.adj.homEquiv, homEquiv, injective, symm.injective
-/
theorem uncurry_injective : Function.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X)) :=
  (Closed.adj.homEquiv _ _).symm.injective

variable (A X)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `uncurry_id_eq_ev` / 定理 `uncurry_id_eq_ev`

English:
theorem uncurry_id_eq_ev
  statement: uncurry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X
  proof: by
  simp [uncurry_eq]

中文:
定理 uncurry_id_eq_ev
  结论: uncurry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X
  证明: by
  simp [uncurry_eq]

Depends on / 依赖: uncurry_eq
-/
theorem uncurry_id_eq_ev : uncurry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X := by
  simp [uncurry_eq]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `curry_id_eq_coev` / 定理 `curry_id_eq_coev`

English:
theorem curry_id_eq_coev
  statement: curry (𝟙 _) = (ihom.coev A).app X
  proof: by
  rw [curry_eq]; rw [(ihom A).map_id (A otimes _)]
  apply comp_id

中文:
定理 curry_id_eq_coev
  结论: curry (𝟙 _) = (ihom.coev A).app X
  证明: by
  rw [curry_eq]; rw [(ihom A).map_id (A otimes _)]
  apply comp_id

Depends on / 依赖: comp_id, curry_eq, map_id, otimes
-/
theorem curry_id_eq_coev : curry (𝟙 _) = (ihom.coev A).app X := by
  rw [curry_eq]; rw [(ihom A).map_id (A otimes _)]
  apply comp_id

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_curry_ihom_ev_app` / 引理 `whiskerLeft_curry_ihom_ev_app`

English:
lemma whiskerLeft_curry_ihom_ev_app
  given: (g : A otimes Y ⟶ X)
  proof: by
  simp [curry_eq]

中文:
引理 whiskerLeft_curry_ihom_ev_app
  条件: (g : A otimes Y ⟶ X)
  证明: by
  simp [curry_eq]

Depends on / 依赖: curry_eq
-/
lemma whiskerLeft_curry_ihom_ev_app (g : A otimes Y ⟶ X) :
    A ◁ curry g ≫ (ihom.ev A).app X = g := by
  simp [curry_eq]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `uncurry_ihom_map` / 定理 `uncurry_ihom_map`

English:
theorem uncurry_ihom_map
  given: (g : Y ⟶ Y')
  proof: by
  apply curry_injective
  rw [curry_uncurry]; rw [curry_natural_right]; rw [← uncurry_id_eq_ev]; rw [curry_uncurry]; rw [id_comp]

中文:
定理 uncurry_ihom_map
  条件: (g : Y ⟶ Y')
  证明: by
  apply curry_injective
  rw [curry_uncurry]; rw [curry_natural_right]; rw [← uncurry_id_eq_ev]; rw [curry_uncurry]; rw [id_comp]

Depends on / 依赖: curry_injective, curry_natural_right, curry_uncurry, id_comp, uncurry_id_eq_ev
-/
theorem uncurry_ihom_map (g : Y ⟶ Y') :
    uncurry ((ihom A).map g) = (ihom.ev A).app Y ≫ g := by
  apply curry_injective
  rw [curry_uncurry]; rw [curry_natural_right]; rw [← uncurry_id_eq_ev]; rw [curry_uncurry]; rw [id_comp]

/--
Definition of `unitNatIso` / `unitNatIso` 的定义

English:
definition unitNatIso
  signature: [Closed (𝟙_ C)]
  body: conjugateIsoEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C)

中文:
定义 unitNatIso
  签名: [Closed (𝟙_ C)]
  定义体: conjugateIsoEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C)

Depends on / 依赖: Adjunction, Adjunction.id, adjunction, conjugateIsoEquiv, ihom.adjunction, leftUnitorNatIso
-/
def unitNatIso [Closed (𝟙_ C)] : 𝟭 C ≅ ihom (𝟙_ C) :=
  conjugateIsoEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C)

/--
Definition of `unitIsoSelf` / `unitIsoSelf` 的定义

English:
definition unitIsoSelf
  signature: [Closed (𝟙_ C)]
  body: (unitNatIso.app X).symm

中文:
定义 unitIsoSelf
  签名: [Closed (𝟙_ C)]
  定义体: (unitNatIso.app X).symm

Depends on / 依赖: unitNatIso, unitNatIso.app
-/
def unitIsoSelf [Closed (𝟙_ C)] : ((𝟙_ C) ⟶[C] X) ≅ X :=
  (unitNatIso.app X).symm

section Pre

variable {A B}
variable [Closed B]

/--
Definition of `pre` / `pre` 的定义

English:
definition pre
  signature: (f : B ⟶ A)
  body: conjugateEquiv (ihom.adjunction _) (ihom.adjunction _) ((tensoringLeft C).map f)

@[reassoc (attr := simp)]

中文:
定义 pre
  签名: (f : B ⟶ A)
  定义体: conjugateEquiv (ihom.adjunction _) (ihom.adjunction _) ((tensoringLeft C).map f)

@[reassoc (attr := simp)]

Depends on / 依赖: adjunction, conjugateEquiv, ihom.adjunction, tensoringLeft
-/
def pre (f : B ⟶ A) : ihom A ⟶ ihom B :=
  conjugateEquiv (ihom.adjunction _) (ihom.adjunction _) ((tensoringLeft C).map f)

@[reassoc (attr := simp)]
/--
theorem `id_tensor_pre_app_comp_ev` / 定理 `id_tensor_pre_app_comp_ev`

English:
theorem id_tensor_pre_app_comp_ev
  given: (f : B ⟶ A) (X : C)
  proof: conjugateEquiv_counit _ _ ((tensoringLeft C).map f) X

@[simp]

中文:
定理 id_tensor_pre_app_comp_ev
  条件: (f : B ⟶ A) (X : C)
  证明: conjugateEquiv_counit _ _ ((tensoringLeft C).map f) X

@[simp]

Depends on / 依赖: conjugateEquiv_counit, tensoringLeft
-/
theorem id_tensor_pre_app_comp_ev (f : B ⟶ A) (X : C) :
    B ◁ (pre f).app X ≫ (ihom.ev B).app X = f ▷ (A ⟶[C] X) ≫ (ihom.ev A).app X :=
  conjugateEquiv_counit _ _ ((tensoringLeft C).map f) X

@[simp]
/--
theorem `uncurry_pre` / 定理 `uncurry_pre`

English:
theorem uncurry_pre
  given: (f : B ⟶ A) (X : C)
  proof: by
  simp [uncurry_eq]

@[reassoc]

中文:
定理 uncurry_pre
  条件: (f : B ⟶ A) (X : C)
  证明: by
  simp [uncurry_eq]

@[reassoc]

Depends on / 依赖: uncurry_eq
-/
theorem uncurry_pre (f : B ⟶ A) (X : C) :
    MonoidalClosed.uncurry ((pre f).app X) = f ▷ _ ≫ (ihom.ev A).app X := by
  simp [uncurry_eq]

@[reassoc]
/--
lemma `curry_pre_app` / 引理 `curry_pre_app`

English:
lemma curry_pre_app
  given: (f : B ⟶ A) {X Y : C} (g : A otimes Y ⟶ X)
  proof: uncurry_injective (by
  rw [uncurry_curry]; rw [uncurry_eq]; rw [MonoidalCategory.whiskerLeft_comp]; rw [assoc]; rw [id_tensor_pre_app_comp_ev]; rw [whisker_exchange_assoc]; rw [whiskerLeft_curry_ihom_ev_app])

@[reassoc (attr := simp)]

中文:
引理 curry_pre_app
  条件: (f : B ⟶ A) {X Y : C} (g : A otimes Y ⟶ X)
  证明: uncurry_injective (by
  rw [uncurry_curry]; rw [uncurry_eq]; rw [MonoidalCategory.whiskerLeft_comp]; rw [assoc]; rw [id_tensor_pre_app_comp_ev]; rw [whisker_exchange_assoc]; rw [whiskerLeft_curry_ihom_ev_app])

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, id_tensor_pre_app_comp_ev, uncurry_curry, uncurry_eq, uncurry_injective, whiskerLeft_comp, whiskerLeft_curry_ihom_ev_app, whisker_exchange_assoc
-/
lemma curry_pre_app (f : B ⟶ A) {X Y : C} (g : A otimes Y ⟶ X) :
    curry g ≫ (pre f).app X = curry (f ▷ _ ≫ g) := uncurry_injective (by
  rw [uncurry_curry]; rw [uncurry_eq]; rw [MonoidalCategory.whiskerLeft_comp]; rw [assoc]; rw [id_tensor_pre_app_comp_ev]; rw [whisker_exchange_assoc]; rw [whiskerLeft_curry_ihom_ev_app])

@[reassoc (attr := simp)]
/--
theorem `coev_app_comp_pre_app` / 定理 `coev_app_comp_pre_app`

English:
theorem coev_app_comp_pre_app
  given: (f : B ⟶ A)
  proof: unit_conjugateEquiv _ _ ((tensoringLeft C).map f) X

@[reassoc]

中文:
定理 coev_app_comp_pre_app
  条件: (f : B ⟶ A)
  证明: unit_conjugateEquiv _ _ ((tensoringLeft C).map f) X

@[reassoc]

Depends on / 依赖: tensoringLeft, unit_conjugateEquiv
-/
theorem coev_app_comp_pre_app (f : B ⟶ A) :
    (ihom.coev A).app X ≫ (pre f).app (A otimes X) = (ihom.coev B).app X ≫ (ihom B).map (f ▷ _) :=
  unit_conjugateEquiv _ _ ((tensoringLeft C).map f) X

@[reassoc]
/--
lemma `uncurry_pre_app` / 引理 `uncurry_pre_app`

English:
lemma uncurry_pre_app
  given: (f : Y ⟶ A ⟶[C] X) (g : B ⟶ A)
  proof: curry_injective (by
    rw [curry_uncurry]; rw [← curry_pre_app]; rw [curry_uncurry])

@[simp]

中文:
引理 uncurry_pre_app
  条件: (f : Y ⟶ A ⟶[C] X) (g : B ⟶ A)
  证明: curry_injective (by
    rw [curry_uncurry]; rw [← curry_pre_app]; rw [curry_uncurry])

@[simp]

Depends on / 依赖: curry_injective, curry_pre_app, curry_uncurry
-/
lemma uncurry_pre_app (f : Y ⟶ A ⟶[C] X) (g : B ⟶ A) :
    uncurry (f ≫ (pre g).app X) = g ▷ _ ≫ uncurry f :=
  curry_injective (by
    rw [curry_uncurry]; rw [← curry_pre_app]; rw [curry_uncurry])

@[simp]
/--
theorem `pre_id` / 定理 `pre_id`

English:
theorem pre_id
  given: (A : C) [Closed A]
  statement: pre (𝟙 A) = 𝟙 _
  proof: by
  rw [pre]; rw [Functor.map_id]
  apply conjugateEquiv_id

@[simp]

中文:
定理 pre_id
  条件: (A : C) [Closed A]
  结论: pre (𝟙 A) = 𝟙 _
  证明: by
  rw [pre]; rw [Functor.map_id]
  apply conjugateEquiv_id

@[simp]

Depends on / 依赖: Functor, Functor.map_id, conjugateEquiv_id, map_id
-/
theorem pre_id (A : C) [Closed A] : pre (𝟙 A) = 𝟙 _ := by
  rw [pre]; rw [Functor.map_id]
  apply conjugateEquiv_id

@[simp]
/--
theorem `pre_map` / 定理 `pre_map`

English:
theorem pre_map
  given: {A₁ A₂ A₃ : C} [Closed A₁] [Closed A₂] [Closed A₃] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
  proof: by
  rw [pre]; rw [pre]; rw [pre]; rw [conjugateEquiv_comp]; rw [(tensoringLeft C).map_comp]

中文:
定理 pre_map
  条件: {A₁ A₂ A₃ : C} [Closed A₁] [Closed A₂] [Closed A₃] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
  证明: by
  rw [pre]; rw [pre]; rw [pre]; rw [conjugateEquiv_comp]; rw [(tensoringLeft C).map_comp]

Depends on / 依赖: conjugateEquiv_comp, map_comp, tensoringLeft
-/
theorem pre_map {A₁ A₂ A₃ : C} [Closed A₁] [Closed A₂] [Closed A₃] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    pre (f ≫ g) = pre g ≫ pre f := by
  rw [pre]; rw [pre]; rw [pre]; rw [conjugateEquiv_comp]; rw [(tensoringLeft C).map_comp]

/--
theorem `pre_comm_ihom_map` / 定理 `pre_comm_ihom_map`

English:
theorem pre_comm_ihom_map
  given: {W X Y Z : C} [Closed W] [Closed X] (f : W ⟶ X) (g : Y ⟶ Z)
  proof: by simp

中文:
定理 pre_comm_ihom_map
  条件: {W X Y Z : C} [Closed W] [Closed X] (f : W ⟶ X) (g : Y ⟶ Z)
  证明: by simp
-/
theorem pre_comm_ihom_map {W X Y Z : C} [Closed W] [Closed X] (f : W ⟶ X) (g : Y ⟶ Z) :
    (pre f).app Y ≫ (ihom W).map g = (ihom X).map g ≫ (pre f).app Z := by simp

end Pre

/-- The internal hom functor given by the monoidal closed structure. -/
@[simps]
/--
Definition of `internalHom` / `internalHom` 的定义

English:
definition internalHom
  signature: [MonoidalClosed C]
  body: ihom X.unop
  map f := pre f.unop

中文:
定义 internalHom
  签名: [MonoidalClosed C]
  定义体: ihom X.unop
  map f := pre f.unop

Depends on / 依赖: X.unop
-/
def internalHom [MonoidalClosed C] : Cᵒᵖ ⥤ C ⥤ C where
  obj X := ihom X.unop
  map f := pre f.unop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonoidalClosed
  signature: C] (X
  body: by
  bdsimp
  infer_instance

中文:
实例 [MonoidalClosed
  签名: C] (X
  定义体: by
  bdsimp
  infer_instance

Depends on / 依赖: bdsimp, infer_instance
-/
instance [MonoidalClosed C] (X : Cᵒᵖ) : (internalHom.obj X).IsRightAdjoint := by
  bdsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The parametrized adjunction between `curriedTensor C : C ⥤ C ⥤ C`
and `internalHom : Cᵒᵖ ⥤ C ⥤ C` -/
@[simps!]
/--
Definition of `internalHomAdjunction₂` / `internalHomAdjunction₂` 的定义

English:
definition internalHomAdjunction₂
  signature: [MonoidalClosed C]
  body: ihom.adjunction _

中文:
定义 internalHomAdjunction₂
  签名: [MonoidalClosed C]
  定义体: ihom.adjunction _

Depends on / 依赖: adjunction, ihom.adjunction
-/
def internalHomAdjunction₂ [MonoidalClosed C] :
    curriedTensor C ⊣₂ internalHom where
  adj _ := ihom.adjunction _

section OfEquiv

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

variable (F : C ⥤ D) {G : D ⥤ C} (adj : F ⊣ G)
  [F.Monoidal] [F.IsEquivalence] [MonoidalClosed D]

/-- Transport the property of being monoidal closed across a monoidal equivalence of categories -/
@[instance_reducible]
/--
Definition of `ofEquiv` / `ofEquiv` 的定义

English:
definition ofEquiv
  signature: : MonoidalClosed C where
  body: { rightAdj := F ⋙ ihom (F.obj X) ⋙ G
      adj := (adj.comp ((ihom.adjunction (F.obj X)).comp
          adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft
            (Iso.compInverseIso (H := adj.toEquivalence) (Functor.Monoidal.commTensorLeft F X)) }

中文:
定义 ofEquiv
  签名: : MonoidalClosed C where
  定义体: { rightAdj := F ⋙ ihom (F.obj X) ⋙ G
      adj := (adj.comp ((ihom.adjunction (F.obj X)).comp
          adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft
            (Iso.compInverseIso (H := adj.toEquivalence) (Functor.Monoidal.commTensorLeft F X)) }

Depends on / 依赖: F.obj, Functor, Functor.Monoidal.commTensorLeft, Iso.compInverseIso, Monoidal, adj.comp, adj.toEquivalence, adj.toEquivalence.symm.toAdjunction, adjunction, commTensorLeft, compInverseIso, ihom.adjunction, infer_instance, mono_of_mono_map, ofNatIsoLeft, rightAdj, sheafToPresheaf, toAdjunction, toEquivalence
-/
noncomputable def ofEquiv : MonoidalClosed C where
  closed X :=
    { rightAdj := F ⋙ ihom (F.obj X) ⋙ G
      adj := (adj.comp ((ihom.adjunction (F.obj X)).comp
          adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft
            (Iso.compInverseIso (H := adj.toEquivalence) (Functor.Monoidal.commTensorLeft F X)) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `ofEquiv_curry_def` / 定理 `ofEquiv_curry_def`

English:
theorem ofEquiv_curry_def
  given: {X Y Z : C} (f : X otimes Y ⟶ Z)
  proof: ofEquiv F adj
    MonoidalClosed.curry f =
      adj.homEquiv Y ((ihom (F.obj X)).obj (F.obj Z))
        (MonoidalClosed.curry (adj.toEquivalence.symm.toAdjunction.homEquiv (F.obj X otimes F.obj Y) Z
        ((Iso.compInverseIso (H := adj.toEquivalence)
          (Functor.Monoidal.commTensorLeft F X

中文:
定理 ofEquiv_curry_def
  条件: {X Y Z : C} (f : X otimes Y ⟶ Z)
  证明: ofEquiv F adj
    MonoidalClosed.curry f =
      adj.homEquiv Y ((ihom (F.obj X)).obj (F.obj Z))
        (MonoidalClosed.curry (adj.toEquivalence.symm.toAdjunction.homEquiv (F.obj X otimes F.obj Y) Z
        ((Iso.compInverseIso (H := adj.toEquivalence)
          (Functor.Monoidal.commTensorLeft F X

Depends on / 依赖: FullSubcategory, NatTrans, NatTrans.naturality, ObjectProperty, ObjectProperty.FullSubcategory.comp_hom, Sheaf.image, Sheaf.toImage, Sheaf.toImage_hom, Subtype, Subtype.ext, comp_hom, congr_arg, f.hom.app, hom.app, i.op, isSeparatedFor, isSeparatedFor.ext, isSheaf_iff_isSheaf_of_type, naturality, obj.map
-/
theorem ofEquiv_curry_def {X Y Z : C} (f : X otimes Y ⟶ Z) :
    letI := ofEquiv F adj
    MonoidalClosed.curry f =
      adj.homEquiv Y ((ihom (F.obj X)).obj (F.obj Z))
        (MonoidalClosed.curry (adj.toEquivalence.symm.toAdjunction.homEquiv (F.obj X otimes F.obj Y) Z
        ((Iso.compInverseIso (H := adj.toEquivalence)
          (Functor.Monoidal.commTensorLeft F X)).hom.app Y ≫ f))) := by
  -- This whole proof used to be `rfl` before https://github.com/leanprover-community/mathlib4/pull/16317.
  change ((adj.comp ((ihom.adjunction (F.obj X)).comp
      adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft _).homEquiv _ _ _ = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  dsimp
  rw [Adjunction.comp_homEquiv]; rw [Adjunction.comp_homEquiv]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `ofEquiv_uncurry_def` / 定理 `ofEquiv_uncurry_def`

English:
theorem ofEquiv_uncurry_def
  given: {X Y Z : C}
  proof: ofEquiv F adj
    forall (f : Y ⟶ (ihom X).obj Z), MonoidalClosed.uncurry f =
      ((Iso.compInverseIso (H := adj.toEquivalence)
          (Functor.Monoidal.commTensorLeft F X)).inv.app Y) ≫
            (adj.toEquivalence.symm.toAdjunction.homEquiv _ _).symm
              (MonoidalClosed.uncurry ((

中文:
定理 ofEquiv_uncurry_def
  条件: {X Y Z : C}
  证明: ofEquiv F adj
    forall (f : Y ⟶ (ihom X).obj Z), MonoidalClosed.uncurry f =
      ((Iso.compInverseIso (H := adj.toEquivalence)
          (Functor.Monoidal.commTensorLeft F X)).inv.app Y) ≫
            (adj.toEquivalence.symm.toAdjunction.homEquiv _ _).symm
              (MonoidalClosed.uncurry ((

Depends on / 依赖: ofEquiv
-/
theorem ofEquiv_uncurry_def {X Y Z : C} :
    letI := ofEquiv F adj
    forall (f : Y ⟶ (ihom X).obj Z), MonoidalClosed.uncurry f =
      ((Iso.compInverseIso (H := adj.toEquivalence)
          (Functor.Monoidal.commTensorLeft F X)).inv.app Y) ≫
            (adj.toEquivalence.symm.toAdjunction.homEquiv _ _).symm
              (MonoidalClosed.uncurry ((adj.homEquiv _ _).symm f)) := by
  intro f
  -- This whole proof used to be `rfl` before https://github.com/leanprover-community/mathlib4/pull/16317.
  change (((adj.comp ((ihom.adjunction (F.obj X)).comp
      adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft _).homEquiv _ _).symm _ = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  dsimp
  rw [Adjunction.comp_homEquiv]; rw [Adjunction.comp_homEquiv]
  rfl

end OfEquiv

-- A closed monoidal category C is always enriched over itself.
-- This section contains the necessary definitions and equalities to endow C with
-- the structure of a C-category, while the instance itself is defined in `Closed/Enrichment`.
-- In particular, we only assume the necessary instances of `Closed x`, rather than assuming
-- C comes with an instance of `MonoidalClosed`
section Enriched

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (x : C) [Closed x]
  body: curry (ρ_ x).hom

中文:
定义 id
  签名: (x : C) [Closed x]
  定义体: curry (ρ_ x).hom
-/
def id (x : C) [Closed x] : 𝟙_ C ⟶ (ihom x).obj x := curry (ρ_ x).hom

/--
Definition of `compTranspose` / `compTranspose` 的定义

English:
definition compTranspose
  signature: (x y z : C) [Closed x] [Closed y]
  body: (α_ x ((ihom x).obj y) ((ihom y).obj z)).inv ≫
    (ihom.ev x).app y ▷ ((ihom y).obj z) ≫ (ihom.ev y).app z

中文:
定义 compTranspose
  签名: (x y z : C) [Closed x] [Closed y]
  定义体: (α_ x ((ihom x).obj y) ((ihom y).obj z)).inv ≫
    (ihom.ev x).app y ▷ ((ihom y).obj z) ≫ (ihom.ev y).app z

Depends on / 依赖: ihom.ev
-/
def compTranspose (x y z : C) [Closed x] [Closed y] : x otimes (ihom x).obj y otimes (ihom y).obj z ⟶ z :=
  (α_ x ((ihom x).obj y) ((ihom y).obj z)).inv ≫
    (ihom.ev x).app y ▷ ((ihom y).obj z) ≫ (ihom.ev y).app z

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (x y z : C) [Closed x] [Closed y]
  body: curry (compTranspose x y z)

中文:
定义 comp
  签名: (x y z : C) [Closed x] [Closed y]
  定义体: curry (compTranspose x y z)

Depends on / 依赖: compTranspose
-/
def comp (x y z : C) [Closed x] [Closed y] : (ihom x).obj y otimes (ihom y).obj z ⟶ (ihom x).obj z :=
  curry (compTranspose x y z)

/--
lemma `id_eq` / 引理 `id_eq`

English:
lemma id_eq
  given: (x : C) [Closed x]
  statement: id x = curry (ρ_ x).hom
  proof: rfl

中文:
引理 id_eq
  条件: (x : C) [Closed x]
  结论: id x = curry (ρ_ x).hom
  证明: rfl
-/
lemma id_eq (x : C) [Closed x] : id x = curry (ρ_ x).hom := rfl

/--
lemma `compTranspose_eq` / 引理 `compTranspose_eq`

English:
lemma compTranspose_eq
  given: (x y z : C) [Closed x] [Closed y]
  proof: rfl

中文:
引理 compTranspose_eq
  条件: (x y z : C) [Closed x] [Closed y]
  证明: rfl
-/
lemma compTranspose_eq (x y z : C) [Closed x] [Closed y] :
    compTranspose x y z = (α_ _ _ _).inv ≫ (ihom.ev x).app y ▷ _ ≫ (ihom.ev y).app z :=
  rfl

/--
lemma `comp_eq` / 引理 `comp_eq`

English:
lemma comp_eq
  given: (x y z : C) [Closed x] [Closed y]
  statement: comp x y z = curry (compTranspose x y z)
  proof: rfl

中文:
引理 comp_eq
  条件: (x y z : C) [Closed x] [Closed y]
  结论: comp x y z = curry (compTranspose x y z)
  证明: rfl
-/
lemma comp_eq (x y z : C) [Closed x] [Closed y] : comp x y z = curry (compTranspose x y z) := rfl

/-!
The proofs of associativity and unitality use the following outline:
  1. Take adjoint transpose on each side of the equality (`uncurry_injective`)
  2. Do whatever rewrites/simps are necessary to apply `uncurry_curry`
  3. Conclude with simp
-/

set_option backward.isDefEq.respectTransparency false in
/-- Left unitality of the enriched structure -/
@[reassoc (attr := simp)]
/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  given: (x y : C) [Closed x]
  proof: by
  apply uncurry_injective
  rw [uncurry_natural_left]; rw [uncurry_natural_left]; rw [comp_eq]; rw [uncurry_curry]; rw [id_eq]; rw [compTranspose_eq]; rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; rw [← uncurry_eq]; rw [uncurry_curry]; rw [triangle_assoc_comp_right_

中文:
引理 id_comp
  条件: (x y : C) [Closed x]
  证明: by
  apply uncurry_injective
  rw [uncurry_natural_left]; rw [uncurry_natural_left]; rw [comp_eq]; rw [uncurry_curry]; rw [id_eq]; rw [compTranspose_eq]; rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; rw [← uncurry_eq]; rw [uncurry_curry]; rw [triangle_assoc_comp_right_

Depends on / 依赖: associator_inv_naturality_middle_assoc, compTranspose_eq, comp_eq, comp_whiskerRight_assoc, id_eq, triangle_assoc_comp_right_assoc, uncurry_curry, uncurry_eq, uncurry_id_eq_ev, uncurry_injective, uncurry_natural_left, whiskerLeft_inv_hom_assoc
-/
lemma id_comp (x y : C) [Closed x] :
    (fun_ ((ihom x).obj y)).inv ≫ id x ▷ _ ≫ comp x x y = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_natural_left]; rw [uncurry_natural_left]; rw [comp_eq]; rw [uncurry_curry]; rw [id_eq]; rw [compTranspose_eq]; rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; rw [← uncurry_eq]; rw [uncurry_curry]; rw [triangle_assoc_comp_right_assoc]; rw [whiskerLeft_inv_hom_assoc]; rw [uncurry_id_eq_ev _ _]

set_option backward.isDefEq.respectTransparency false in
/-- Right unitality of the enriched structure -/
@[reassoc (attr := simp)]
/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  given: (x y : C) [Closed x] [Closed y]
  proof: by
  apply uncurry_injective
  rw [uncurry_natural_left]; rw [uncurry_natural_left]; rw [comp_eq]; rw [uncurry_curry]; rw [compTranspose_eq]; rw [associator_inv_naturality_right_assoc]; rw [← rightUnitor_tensor_inv_assoc]; rw [whisker_exchange_assoc]; rw [← rightUnitor_inv_naturality_assoc]; rw [← u

中文:
引理 comp_id
  条件: (x y : C) [Closed x] [Closed y]
  证明: by
  apply uncurry_injective
  rw [uncurry_natural_left]; rw [uncurry_natural_left]; rw [comp_eq]; rw [uncurry_curry]; rw [compTranspose_eq]; rw [associator_inv_naturality_right_assoc]; rw [← rightUnitor_tensor_inv_assoc]; rw [whisker_exchange_assoc]; rw [← rightUnitor_inv_naturality_assoc]; rw [← u

Depends on / 依赖: Functor, Functor.id_obj, associator_inv_naturality_right_assoc, compTranspose_eq, comp_eq, id_eq, id_obj, rightUnitor_inv_naturality_assoc, rightUnitor_tensor_inv_assoc, uncurry_curry, uncurry_id_eq_ev, uncurry_injective, uncurry_natural_left, whisker_exchange_assoc
-/
lemma comp_id (x y : C) [Closed x] [Closed y] :
    (ρ_ ((ihom x).obj y)).inv ≫ _ ◁ id y ≫ comp x y y = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_natural_left]; rw [uncurry_natural_left]; rw [comp_eq]; rw [uncurry_curry]; rw [compTranspose_eq]; rw [associator_inv_naturality_right_assoc]; rw [← rightUnitor_tensor_inv_assoc]; rw [whisker_exchange_assoc]; rw [← rightUnitor_inv_naturality_assoc]; rw [← uncurry_id_eq_ev y y]
  simp only [Functor.id_obj]
  rw [← uncurry_natural_left]
  simp [id_eq, uncurry_id_eq_ev]

set_option backward.isDefEq.respectTransparency false in
/-- Associativity of the enriched structure -/
@[reassoc]
/--
lemma `assoc` / 引理 `assoc`

English:
lemma assoc
  given: (w x y z : C) [Closed w] [Closed x] [Closed y]
  proof: by
  apply uncurry_injective
  simp only [uncurry_natural_left, comp_eq]
  rw [uncurry_curry]; rw [uncurry_curry]; simp only [compTranspose_eq]
  rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; dsimp
  rw [← uncurry_eq]; rw [uncurry_curry]; rw [associator_inv_naturality_

中文:
引理 assoc
  条件: (w x y z : C) [Closed w] [Closed x] [Closed y]
  证明: by
  apply uncurry_injective
  simp only [uncurry_natural_left, comp_eq]
  rw [uncurry_curry]; rw [uncurry_curry]; simp only [compTranspose_eq]
  rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; dsimp
  rw [← uncurry_eq]; rw [uncurry_curry]; rw [associator_inv_naturality_

Depends on / 依赖: associator_inv_naturality_middle_assoc, associator_inv_naturality_right_assoc, compTranspose_eq, comp_eq, comp_whiskerRight_assoc, uncurry_curry, uncurry_eq, uncurry_injective, uncurry_natural_left, whisker_exchange_assoc
-/
lemma assoc (w x y z : C) [Closed w] [Closed x] [Closed y] :
    (α_ _ _ _).inv ≫ comp w x y ▷ _ ≫ comp w y z = _ ◁ comp x y z ≫ comp w x z := by
  apply uncurry_injective
  simp only [uncurry_natural_left, comp_eq]
  rw [uncurry_curry]; rw [uncurry_curry]; simp only [compTranspose_eq]
  rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; dsimp
  rw [← uncurry_eq]; rw [uncurry_curry]; rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]; rw [← uncurry_eq]; rw [uncurry_curry]
  simp

end Enriched

section OrdinaryEnriched

/--
Definition of `curry'` / `curry'` 的定义

English:
definition curry'
  signature: {X Y : C} [Closed X] (f : X ⟶ Y)
  body: curry ((ρ_ _).hom ≫ f)

中文:
定义 curry'
  签名: {X Y : C} [Closed X] (f : X ⟶ Y)
  定义体: curry ((ρ_ _).hom ≫ f)
-/
def curry' {X Y : C} [Closed X] (f : X ⟶ Y) : 𝟙_ C ⟶ (ihom X).obj Y :=
  curry ((ρ_ _).hom ≫ f)

/--
Definition of `uncurry'` / `uncurry'` 的定义

English:
definition uncurry'
  signature: {X Y : C} [Closed X] (g : 𝟙_ C ⟶ (ihom X).obj Y)
  body: (ρ_ _).inv ≫ uncurry g

中文:
定义 uncurry'
  签名: {X Y : C} [Closed X] (g : 𝟙_ C ⟶ (ihom X).obj Y)
  定义体: (ρ_ _).inv ≫ uncurry g

Depends on / 依赖: uncurry
-/
def uncurry' {X Y : C} [Closed X] (g : 𝟙_ C ⟶ (ihom X).obj Y) : X ⟶ Y :=
  (ρ_ _).inv ≫ uncurry g

/-- `curry'` and `uncurry'` are inverse bijections. -/
@[simp]
/--
lemma `curry'_uncurry'` / 引理 `curry'_uncurry'`

English:
lemma curry'_uncurry'
  given: {X Y : C} [Closed X] (g : 𝟙_ C ⟶ (ihom X).obj Y)
  proof: by
  simp [curry', uncurry']

中文:
引理 curry'_uncurry'
  条件: {X Y : C} [Closed X] (g : 𝟙_ C ⟶ (ihom X).obj Y)
  证明: by
  simp [curry', uncurry']
-/
lemma curry'_uncurry' {X Y : C} [Closed X] (g : 𝟙_ C ⟶ (ihom X).obj Y) :
    curry' (uncurry' g) = g := by
  simp [curry', uncurry']

/-- `curry'` and `uncurry'` are inverse bijections. -/
@[simp]
/--
lemma `uncurry'_curry'` / 引理 `uncurry'_curry'`

English:
lemma uncurry'_curry'
  given: {X Y : C} [Closed X] (f : X ⟶ Y)
  proof: by
  simp [curry', uncurry']

中文:
引理 uncurry'_curry'
  条件: {X Y : C} [Closed X] (f : X ⟶ Y)
  证明: by
  simp [curry', uncurry']
-/
lemma uncurry'_curry' {X Y : C} [Closed X] (f : X ⟶ Y) :
    uncurry' (curry' f) = f := by
  simp [curry', uncurry']

/-- The bijection `(X ⟶ Y) ≃ (𝟙_ C ⟶ (ihom X).obj Y)` in a monoidal closed category. -/
@[simps]
/--
Definition of `curryHomEquiv'` / `curryHomEquiv'` 的定义

English:
definition curryHomEquiv'
  signature: {X Y : C} [Closed X]
  body: curry'
  invFun := uncurry'
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 curryHomEquiv'
  签名: {X Y : C} [Closed X]
  定义体: curry'
  invFun := uncurry'
  left_inv _ := by simp
  right_inv _ := by simp
-/
def curryHomEquiv' {X Y : C} [Closed X] :
    (X ⟶ Y) ≃ (𝟙_ C ⟶ (ihom X).obj Y) where
  toFun := curry'
  invFun := uncurry'
  left_inv _ := by simp
  right_inv _ := by simp

/--
lemma `curry'_injective` / 引理 `curry'_injective`

English:
lemma curry'_injective
  given: {X Y : C} [Closed X] {f f' : X ⟶ Y} (h : curry' f = curry' f')
  proof: curryHomEquiv'.injective h

中文:
引理 curry'_injective
  条件: {X Y : C} [Closed X] {f f' : X ⟶ Y} (h : curry' f = curry' f')
  证明: curryHomEquiv'.injective h
-/
lemma curry'_injective {X Y : C} [Closed X] {f f' : X ⟶ Y} (h : curry' f = curry' f') :
    f = f' :=
  curryHomEquiv'.injective h

/--
lemma `uncurry'_injective` / 引理 `uncurry'_injective`

English:
lemma uncurry'_injective
  statement: {X Y : C} [Closed X] {f f' : 𝟙_ C ⟶ (ihom X).obj Y}
  proof: curryHomEquiv'.symm.injective h

@[simp]

中文:
引理 uncurry'_injective
  结论: {X Y : C} [Closed X] {f f' : 𝟙_ C ⟶ (ihom X).obj Y}
  证明: curryHomEquiv'.symm.injective h

@[simp]
-/
lemma uncurry'_injective {X Y : C} [Closed X] {f f' : 𝟙_ C ⟶ (ihom X).obj Y}
    (h : uncurry' f = uncurry' f') : f = f' :=
  curryHomEquiv'.symm.injective h

@[simp]
/--
lemma `curry'_id` / 引理 `curry'_id`

English:
lemma curry'_id
  given: (X : C) [Closed X]
  statement: curry' (𝟙 X) = id X
  proof: by
  dsimp [curry']
  rw [Category.comp_id]
  rfl

@[reassoc]

中文:
引理 curry'_id
  条件: (X : C) [Closed X]
  结论: curry' (𝟙 X) = id X
  证明: by
  dsimp [curry']
  rw [Category.comp_id]
  rfl

@[reassoc]
-/
lemma curry'_id (X : C) [Closed X] : curry' (𝟙 X) = id X := by
  dsimp [curry']
  rw [Category.comp_id]
  rfl

@[reassoc]
/--
lemma `whiskerLeft_curry'_ihom_ev_app` / 引理 `whiskerLeft_curry'_ihom_ev_app`

English:
lemma whiskerLeft_curry'_ihom_ev_app
  given: {X Y : C} [Closed X] (f : X ⟶ Y)
  proof: by
  dsimp [curry']
  simp only [whiskerLeft_curry_ihom_ev_app]

中文:
引理 whiskerLeft_curry'_ihom_ev_app
  条件: {X Y : C} [Closed X] (f : X ⟶ Y)
  证明: by
  dsimp [curry']
  simp only [whiskerLeft_curry_ihom_ev_app]

Depends on / 依赖: whiskerLeft_curry_ihom_ev_app
-/
lemma whiskerLeft_curry'_ihom_ev_app {X Y : C} [Closed X] (f : X ⟶ Y) :
    X ◁ curry' f ≫ (ihom.ev X).app Y = (ρ_ _).hom ≫ f := by
  dsimp [curry']
  simp only [whiskerLeft_curry_ihom_ev_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `curry'_whiskerRight_comp` / 引理 `curry'_whiskerRight_comp`

English:
lemma curry'_whiskerRight_comp
  given: {X Y Z : C} [Closed X] [Closed Y] (f : X ⟶ Y)
  proof: by
  rw [← cancel_epi (fun_ _).inv]; rw [Iso.inv_hom_id_assoc]
  apply uncurry_injective
  rw [uncurry_pre]; rw [comp_eq]; rw [← curry_natural_left]; rw [← curry_natural_left]; rw [uncurry_curry]; rw [compTranspose_eq]; rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; rw 

中文:
引理 curry'_whiskerRight_comp
  条件: {X Y Z : C} [Closed X] [Closed Y] (f : X ⟶ Y)
  证明: by
  rw [← cancel_epi (fun_ _).inv]; rw [Iso.inv_hom_id_assoc]
  apply uncurry_injective
  rw [uncurry_pre]; rw [comp_eq]; rw [← curry_natural_left]; rw [← curry_natural_left]; rw [uncurry_curry]; rw [compTranspose_eq]; rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; rw 
-/
lemma curry'_whiskerRight_comp {X Y Z : C} [Closed X] [Closed Y] (f : X ⟶ Y) :
    curry' f ▷ _ ≫ comp X Y Z = (fun_ _).hom ≫ (pre f).app Z := by
  rw [← cancel_epi (fun_ _).inv]; rw [Iso.inv_hom_id_assoc]
  apply uncurry_injective
  rw [uncurry_pre]; rw [comp_eq]; rw [← curry_natural_left]; rw [← curry_natural_left]; rw [uncurry_curry]; rw [compTranspose_eq]; rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; rw [whiskerLeft_curry'_ihom_ev_app]; rw [comp_whiskerRight_assoc]; rw [triangle_assoc_comp_right_assoc]; rw [whiskerLeft_inv_hom_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `whiskerLeft_curry'_comp` / 引理 `whiskerLeft_curry'_comp`

English:
lemma whiskerLeft_curry'_comp
  given: {X Y Z : C} [Closed X] [Closed Y] (f : Y ⟶ Z)
  proof: by
  rw [← cancel_epi (ρ_ _).inv]; rw [Iso.inv_hom_id_assoc]
  apply uncurry_injective
  rw [uncurry_ihom_map]; rw [comp_eq]; rw [← curry_natural_left]; rw [← curry_natural_left]; rw [uncurry_curry]; rw [compTranspose_eq]; rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]
  dsi

中文:
引理 whiskerLeft_curry'_comp
  条件: {X Y Z : C} [Closed X] [Closed Y] (f : Y ⟶ Z)
  证明: by
  rw [← cancel_epi (ρ_ _).inv]; rw [Iso.inv_hom_id_assoc]
  apply uncurry_injective
  rw [uncurry_ihom_map]; rw [comp_eq]; rw [← curry_natural_left]; rw [← curry_natural_left]; rw [uncurry_curry]; rw [compTranspose_eq]; rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]
  dsi
-/
lemma whiskerLeft_curry'_comp {X Y Z : C} [Closed X] [Closed Y] (f : Y ⟶ Z) :
    _ ◁ curry' f ≫ comp X Y Z = (ρ_ _).hom ≫ (ihom X).map f := by
  rw [← cancel_epi (ρ_ _).inv]; rw [Iso.inv_hom_id_assoc]
  apply uncurry_injective
  rw [uncurry_ihom_map]; rw [comp_eq]; rw [← curry_natural_left]; rw [← curry_natural_left]; rw [uncurry_curry]; rw [compTranspose_eq]; rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]
  dsimp
  rw [whiskerLeft_curry'_ihom_ev_app]; rw [whiskerLeft_rightUnitor_inv]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id_assoc]; rw [Iso.hom_inv_id_assoc]; rw [Iso.inv_hom_id_assoc]

/--
lemma `curry'_ihom_map` / 引理 `curry'_ihom_map`

English:
lemma curry'_ihom_map
  given: {X Y Z : C} [Closed X] (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  simp only [curry', ← curry_natural_right, Category.assoc]

中文:
引理 curry'_ihom_map
  条件: {X Y Z : C} [Closed X] (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  simp only [curry', ← curry_natural_right, Category.assoc]
-/
lemma curry'_ihom_map {X Y Z : C} [Closed X] (f : X ⟶ Y) (g : Y ⟶ Z) :
    curry' f ≫ (ihom X).map g = curry' (f ≫ g) := by
  simp only [curry', ← curry_natural_right, Category.assoc]

/--
lemma `curry'_comp` / 引理 `curry'_comp`

English:
lemma curry'_comp
  given: {X Y Z : C} [Closed X] [Closed Y] (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  rw [tensorHom_def_assoc]; rw [whiskerLeft_curry'_comp]; rw [MonoidalCategory.whiskerRight_id]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id_assoc]; rw [← unitors_equal]; rw [Iso.inv_hom_id_assoc]; rw [curry'_ihom_map]

中文:
引理 curry'_comp
  条件: {X Y Z : C} [Closed X] [Closed Y] (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  rw [tensorHom_def_assoc]; rw [whiskerLeft_curry'_comp]; rw [MonoidalCategory.whiskerRight_id]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id_assoc]; rw [← unitors_equal]; rw [Iso.inv_hom_id_assoc]; rw [curry'_ihom_map]
-/
lemma curry'_comp {X Y Z : C} [Closed X] [Closed Y] (f : X ⟶ Y) (g : Y ⟶ Z) :
    curry' (f ≫ g) = (fun_ (𝟙_ C)).inv ≫ (curry' f otimesₘ curry' g) ≫ comp X Y Z := by
  rw [tensorHom_def_assoc]; rw [whiskerLeft_curry'_comp]; rw [MonoidalCategory.whiskerRight_id]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id_assoc]; rw [← unitors_equal]; rw [Iso.inv_hom_id_assoc]; rw [curry'_ihom_map]

end OrdinaryEnriched

end MonoidalClosed

end CategoryTheory
