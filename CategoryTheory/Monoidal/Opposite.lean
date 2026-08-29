/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
public import Mathlib.Tactic.CategoryTheory.CancelIso

/-!
# Monoidal opposites

We write `Cᵐᵒᵖ` for the monoidal opposite of a monoidal category `C`.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe v₁ v₂ u₁ u₂

variable {C : Type u₁}

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

/--
Definition of `MonoidalOpposite` / `MonoidalOpposite` 的定义

English:
structure MonoidalOpposite
  parameters: (C : Type u₁)
  (no additional axioms)

中文:
结构 MonoidalOpposite
  参数: (C : 类型u₁)
  (无附加公理)
-/
structure MonoidalOpposite (C : Type u₁) where
  /-- The object of `MonoidalOpposite C` that represents `x : C`. -/ mop ::
  /-- The object of `C` represented by `x : MonoidalOpposite C`. -/ unmop : C

namespace MonoidalOpposite

@[inherit_doc]
notation:max C "ᴹᵒᵖ" => MonoidalOpposite C

/--
theorem `mop_injective` / 定理 `mop_injective`

English:
theorem mop_injective
  statement: Function.Injective (mop : C -> Cᴹᵒᵖ)
  proof: @mop.inj C

中文:
定理 mop_injective
  结论: Function.Injective (mop : C -> Cᴹᵒᵖ)
  证明: @mop.inj C

Depends on / 依赖: mop.inj
-/
theorem mop_injective : Function.Injective (mop : C -> Cᴹᵒᵖ) := @mop.inj C

/--
theorem `unmop_injective` / 定理 `unmop_injective`

English:
theorem unmop_injective
  statement: Function.Injective (unmop : Cᴹᵒᵖ -> C)
  proof: fun _ _ h => congrArg mop h

中文:
定理 unmop_injective
  结论: Function.Injective (unmop : Cᴹᵒᵖ -> C)
  证明: fun _ _ h => congrArg mop h
-/
theorem unmop_injective : Function.Injective (unmop : Cᴹᵒᵖ -> C) :=
  fun _ _ h => congrArg mop h

/--
theorem `mop_inj_iff` / 定理 `mop_inj_iff`

English:
theorem mop_inj_iff
  given: (x y : C)
  statement: mop x = mop y ↔ x = y
  proof: mop_injective.eq_iff

@[simp]

中文:
定理 mop_inj_iff
  条件: (x y : C)
  结论: mop x = mop y ↔ x = y
  证明: mop_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, mop_injective, mop_injective.eq_iff
-/
theorem mop_inj_iff (x y : C) : mop x = mop y ↔ x = y := mop_injective.eq_iff

@[simp]
/--
theorem `unmop_inj_iff` / 定理 `unmop_inj_iff`

English:
theorem unmop_inj_iff
  given: (x y : Cᴹᵒᵖ)
  statement: unmop x = unmop y ↔ x = y
  proof: unmop_injective.eq_iff

@[simp]

中文:
定理 unmop_inj_iff
  条件: (x y : Cᴹᵒᵖ)
  结论: unmop x = unmop y ↔ x = y
  证明: unmop_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, unmop_injective, unmop_injective.eq_iff
-/
theorem unmop_inj_iff (x y : Cᴹᵒᵖ) : unmop x = unmop y ↔ x = y := unmop_injective.eq_iff

@[simp]
/--
theorem `mop_unmop` / 定理 `mop_unmop`

English:
theorem mop_unmop
  given: (X : Cᴹᵒᵖ)
  statement: mop (unmop X) = X
  proof: rfl

中文:
定理 mop_unmop
  条件: (X : Cᴹᵒᵖ)
  结论: mop (unmop X) = X
  证明: rfl
-/
theorem mop_unmop (X : Cᴹᵒᵖ) : mop (unmop X) = X := rfl

-- can't be simp bc after putting the lhs in whnf it's `X = X`
/--
theorem `unmop_mop` / 定理 `unmop_mop`

English:
theorem unmop_mop
  given: (X : C)
  statement: unmop (mop X) = X
  proof: rfl

中文:
定理 unmop_mop
  条件: (X : C)
  结论: unmop (mop X) = X
  证明: rfl
-/
theorem unmop_mop (X : C) : unmop (mop X) = X := rfl

/--
Instance `monoidalOppositeCategory` / 实例 `monoidalOppositeCategory`

English:
instance monoidalOppositeCategory
  signature: [Category.{v₁} C]
  body: (unmop X ⟶ unmop Y)ᴹᵒᵖ
  id X := mop (𝟙 (unmop X))
  comp f g := mop (unmop f ≫ unmop g)

中文:
实例 monoidalOppositeCategory
  签名: [Category.{v₁} C]
  定义体: (unmop X ⟶ unmop Y)ᴹᵒᵖ
  id X := mop (𝟙 (unmop X))
  comp f g := mop (unmop f ≫ unmop g)
-/
instance monoidalOppositeCategory [Category.{v₁} C] : Category Cᴹᵒᵖ where
  Hom X Y := (unmop X ⟶ unmop Y)ᴹᵒᵖ
  id X := mop (𝟙 (unmop X))
  comp f g := mop (unmop f ≫ unmop g)

end MonoidalOpposite

end CategoryTheory

open CategoryTheory

open CategoryTheory.MonoidalOpposite

variable [Category.{v₁} C]

/--
Definition of `Quiver.Hom.mop` / `Quiver.Hom.mop` 的定义

English:
definition Quiver.Hom.mop
  signature: {X Y : C} (f : X ⟶ Y)
  body: MonoidalOpposite.mop f

中文:
定义 Quiver.Hom.mop
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: MonoidalOpposite.mop f

Depends on / 依赖: MonoidalOpposite, MonoidalOpposite.mop
-/
def Quiver.Hom.mop {X Y : C} (f : X ⟶ Y) : mop X ⟶ mop Y := MonoidalOpposite.mop f

/--
Definition of `Quiver.Hom.unmop` / `Quiver.Hom.unmop` 的定义

English:
definition Quiver.Hom.unmop
  signature: {X Y : Cᴹᵒᵖ} (f : X ⟶ Y)
  body: MonoidalOpposite.unmop f

中文:
定义 Quiver.Hom.unmop
  签名: {X Y : Cᴹᵒᵖ} (f : X ⟶ Y)
  定义体: MonoidalOpposite.unmop f

Depends on / 依赖: MonoidalOpposite, MonoidalOpposite.unmop
-/
def Quiver.Hom.unmop {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) : unmop X ⟶ unmop Y := MonoidalOpposite.unmop f

namespace Quiver.Hom

open MonoidalOpposite renaming mop -> mop', unmop -> unmop'

/--
theorem `mop_inj` / 定理 `mop_inj`

English:
theorem mop_inj
  given: {X Y : C}
  proof: fun _ _ H => congr_arg Quiver.Hom.unmop H

中文:
定理 mop_inj
  条件: {X Y : C}
  证明: fun _ _ H => congr_arg Quiver.Hom.unmop H

Depends on / 依赖: Quiver, Quiver.Hom.unmop, congr_arg
-/
theorem mop_inj {X Y : C} :
    Function.Injective (Quiver.Hom.mop : (X ⟶ Y) -> (mop' X ⟶ mop' Y)) :=
  fun _ _ H => congr_arg Quiver.Hom.unmop H

/--
theorem `unmop_inj` / 定理 `unmop_inj`

English:
theorem unmop_inj
  given: {X Y : Cᴹᵒᵖ}
  proof: fun _ _ H => congr_arg Quiver.Hom.mop H

@[simp]

中文:
定理 unmop_inj
  条件: {X Y : Cᴹᵒᵖ}
  证明: fun _ _ H => congr_arg Quiver.Hom.mop H

@[simp]

Depends on / 依赖: Quiver, Quiver.Hom.mop, congr_arg
-/
theorem unmop_inj {X Y : Cᴹᵒᵖ} :
    Function.Injective (Quiver.Hom.unmop : (X ⟶ Y) -> (unmop' X ⟶ unmop' Y)) :=
  fun _ _ H => congr_arg Quiver.Hom.mop H

@[simp]
/--
theorem `unmop_mop` / 定理 `unmop_mop`

English:
theorem unmop_mop
  given: {X Y : C} {f : X ⟶ Y}
  statement: f.mop.unmop = f
  proof: rfl

@[simp]

中文:
定理 unmop_mop
  条件: {X Y : C} {f : X ⟶ Y}
  结论: f.mop.unmop = f
  证明: rfl

@[simp]
-/
theorem unmop_mop {X Y : C} {f : X ⟶ Y} : f.mop.unmop = f :=
  rfl

@[simp]
/--
theorem `mop_unmop` / 定理 `mop_unmop`

English:
theorem mop_unmop
  given: {X Y : Cᴹᵒᵖ} {f : X ⟶ Y}
  statement: f.unmop.mop = f
  proof: rfl

中文:
定理 mop_unmop
  条件: {X Y : Cᴹᵒᵖ} {f : X ⟶ Y}
  结论: f.unmop.mop = f
  证明: rfl
-/
theorem mop_unmop {X Y : Cᴹᵒᵖ} {f : X ⟶ Y} : f.unmop.mop = f :=
  rfl

end Quiver.Hom

namespace CategoryTheory

@[simp]
/--
theorem `mop_comp` / 定理 `mop_comp`

English:
theorem mop_comp
  given: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
  proof: rfl

@[simp]

中文:
定理 mop_comp
  条件: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
  证明: rfl

@[simp]
-/
theorem mop_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} :
    (f ≫ g).mop = f.mop ≫ g.mop := rfl

@[simp]
/--
theorem `mop_id` / 定理 `mop_id`

English:
theorem mop_id
  given: {X : C}
  statement: (𝟙 X).mop = 𝟙 (mop X)
  proof: rfl

@[simp]

中文:
定理 mop_id
  条件: {X : C}
  结论: (𝟙 X).mop = 𝟙 (mop X)
  证明: rfl

@[simp]
-/
theorem mop_id {X : C} : (𝟙 X).mop = 𝟙 (mop X) := rfl

@[simp]
/--
theorem `unmop_comp` / 定理 `unmop_comp`

English:
theorem unmop_comp
  given: {X Y Z : Cᴹᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z}
  proof: rfl

@[simp]

中文:
定理 unmop_comp
  条件: {X Y Z : Cᴹᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z}
  证明: rfl

@[simp]
-/
theorem unmop_comp {X Y Z : Cᴹᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} :
    (f ≫ g).unmop = f.unmop ≫ g.unmop := rfl

@[simp]
/--
theorem `unmop_id` / 定理 `unmop_id`

English:
theorem unmop_id
  given: {X : Cᴹᵒᵖ}
  statement: (𝟙 X).unmop = 𝟙 (unmop X)
  proof: rfl

@[simp]

中文:
定理 unmop_id
  条件: {X : Cᴹᵒᵖ}
  结论: (𝟙 X).unmop = 𝟙 (unmop X)
  证明: rfl

@[simp]
-/
theorem unmop_id {X : Cᴹᵒᵖ} : (𝟙 X).unmop = 𝟙 (unmop X) := rfl

@[simp]
/--
theorem `unmop_id_mop` / 定理 `unmop_id_mop`

English:
theorem unmop_id_mop
  given: {X : C}
  statement: (𝟙 (mop X)).unmop = 𝟙 X
  proof: rfl

@[simp]

中文:
定理 unmop_id_mop
  条件: {X : C}
  结论: (𝟙 (mop X)).unmop = 𝟙 X
  证明: rfl

@[simp]
-/
theorem unmop_id_mop {X : C} : (𝟙 (mop X)).unmop = 𝟙 X := rfl

@[simp]
/--
theorem `mop_id_unmop` / 定理 `mop_id_unmop`

English:
theorem mop_id_unmop
  given: {X : Cᴹᵒᵖ}
  statement: (𝟙 (unmop X)).mop = 𝟙 X
  proof: rfl

中文:
定理 mop_id_unmop
  条件: {X : Cᴹᵒᵖ}
  结论: (𝟙 (unmop X)).mop = 𝟙 X
  证明: rfl
-/
theorem mop_id_unmop {X : Cᴹᵒᵖ} : (𝟙 (unmop X)).mop = 𝟙 X := rfl

-- aesop prefers this lemma as a safe apply over Quiver.Hom.unmop_inj
/--
lemma `MonoidalOpposite.hom_ext` / 引理 `MonoidalOpposite.hom_ext`

English:
lemma MonoidalOpposite.hom_ext
  given: {x y : Cᴹᵒᵖ} {f g : x ⟶ y} (h : f.unmop = g.unmop)
  proof: Quiver.Hom.unmop_inj h

中文:
引理 MonoidalOpposite.hom_ext
  条件: {x y : Cᴹᵒᵖ} {f g : x ⟶ y} (h : f.unmop = g.unmop)
  证明: Quiver.Hom.unmop_inj h

Depends on / 依赖: Quiver, Quiver.Hom.unmop_inj, unmop_inj
-/
lemma MonoidalOpposite.hom_ext {x y : Cᴹᵒᵖ} {f g : x ⟶ y} (h : f.unmop = g.unmop) :
    f = g :=
  Quiver.Hom.unmop_inj h

variable (C)

/-- The identity functor on `C`, viewed as a functor from `C` to its monoidal opposite. -/
@[simps obj map] -- need to specify `obj, map` or else we generate `mopFunctor_obj_unmop`
/--
Definition of `mopFunctor` / `mopFunctor` 的定义

English:
definition mopFunctor
  signature: : C ⥤ Cᴹᵒᵖ
  body: Functor.mk mop .mop

中文:
定义 mopFunctor
  签名: : C ⥤ Cᴹᵒᵖ
  定义体: Functor.mk mop .mop

Depends on / 依赖: Functor, Functor.mk
-/
def mopFunctor : C ⥤ Cᴹᵒᵖ := Functor.mk mop .mop
/-- The identity functor on `C`, viewed as a functor from the monoidal opposite of `C` to `C`. -/
@[simps obj map] -- not necessary but the symmetry with `mopFunctor` looks nicer
/--
Definition of `unmopFunctor` / `unmopFunctor` 的定义

English:
definition unmopFunctor
  signature: : Cᴹᵒᵖ ⥤ C
  body: Functor.mk unmop .unmop

中文:
定义 unmopFunctor
  签名: : Cᴹᵒᵖ ⥤ C
  定义体: Functor.mk unmop .unmop

Depends on / 依赖: Functor, Functor.mk
-/
def unmopFunctor : Cᴹᵒᵖ ⥤ C := Functor.mk unmop .unmop

variable {C}

namespace Iso

/--
Definition of `mop` / `mop` 的定义

English:
abbreviation mop
  signature: {X Y : C} (f : X ≅ Y)
  body: (mopFunctor C).mapIso f

中文:
缩写 mop
  签名: {X Y : C} (f : X ≅ Y)
  定义体: (mopFunctor C).mapIso f

Depends on / 依赖: isFinite, mapIso, mopFunctor, yoneda_obj_isGeneratedBy
-/
abbrev mop {X Y : C} (f : X ≅ Y) : mop X ≅ mop Y := (mopFunctor C).mapIso f

/--
Definition of `unmop` / `unmop` 的定义

English:
abbreviation unmop
  signature: {X Y : Cᴹᵒᵖ} (f : X ≅ Y)
  body: (unmopFunctor C).mapIso f

中文:
缩写 unmop
  签名: {X Y : Cᴹᵒᵖ} (f : X ≅ Y)
  定义体: (unmopFunctor C).mapIso f

Depends on / 依赖: mapIso, unmopFunctor
-/
abbrev unmop {X Y : Cᴹᵒᵖ} (f : X ≅ Y) : unmop X ≅ unmop Y := (unmopFunctor C).mapIso f

end Iso

namespace IsIso

instance {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso f.mop :=
  (mopFunctor C).map_isIso f
instance {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) [IsIso f] : IsIso f.unmop :=
  (unmopFunctor C).map_isIso f

end IsIso

variable [MonoidalCategory.{v₁} C]

open Opposite MonoidalCategory CategoryTheory.Functor LaxMonoidal OplaxMonoidal

set_option backward.defeqAttrib.useBackward true in
/--
Instance `monoidalCategoryOp` / 实例 `monoidalCategoryOp`

English:
instance monoidalCategoryOp
  signature: : MonoidalCategory Cᵒᵖ where
  body: op (unop X otimes unop Y)
  whiskerLeft X _ _ f := (X.unop ◁ f.unop).op
  whiskerRight f X := (f.unop ▷ X.unop).op
  tensorHom f g := (f.unop otimesₘ g.unop).op
  tensorHom_def _ _ := Quiver.Hom.unop_inj (tensorHom_def' _ _)
tensorHom_comp_tensorHom _ _ _ _ := Quiver.Hom.unop_inj by simp
  tensorUni

中文:
实例 monoidalCategoryOp
  签名: : MonoidalCategory Cᵒᵖ where
  定义体: op (unop X otimes unop Y)
  whiskerLeft X _ _ f := (X.unop ◁ f.unop).op
  whiskerRight f X := (f.unop ▷ X.unop).op
  tensorHom f g := (f.unop otimesₘ g.unop).op
  tensorHom_def _ _ := Quiver.Hom.unop_inj (tensorHom_def' _ _)
tensorHom_comp_tensorHom _ _ _ _ := Quiver.Hom.unop_inj by simp
  tensorUni

Depends on / 依赖: otimes
-/
instance monoidalCategoryOp : MonoidalCategory Cᵒᵖ where
  tensorObj X Y := op (unop X otimes unop Y)
  whiskerLeft X _ _ f := (X.unop ◁ f.unop).op
  whiskerRight f X := (f.unop ▷ X.unop).op
  tensorHom f g := (f.unop otimesₘ g.unop).op
  tensorHom_def _ _ := Quiver.Hom.unop_inj (tensorHom_def' _ _)
tensorHom_comp_tensorHom _ _ _ _ := Quiver.Hom.unop_inj by simp
  tensorUnit := op (𝟙_ C)
  associator X Y Z := (α_ (unop X) (unop Y) (unop Z)).symm.op
  leftUnitor X := (fun_ (unop X)).symm.op
  rightUnitor X := (ρ_ (unop X)).symm.op
associator_naturality f g h := Quiver.Hom.unop_inj by simp
leftUnitor_naturality f := Quiver.Hom.unop_inj by simp
rightUnitor_naturality f := Quiver.Hom.unop_inj by simp
triangle X Y := Quiver.Hom.unop_inj by dsimp; monoidal_coherence
pentagon W X Y Z := Quiver.Hom.unop_inj by dsimp; monoidal_coherence

section OppositeLemmas

/--
lemma `op_tensorObj` / 引理 `op_tensorObj`

English:
lemma op_tensorObj
  given: (X Y : C)
  statement: op (X otimes Y) = op X otimes op Y
  proof: rfl

中文:
引理 op_tensorObj
  条件: (X Y : C)
  结论: op (X otimes Y) = op X otimes op Y
  证明: rfl
-/
@[simp] lemma op_tensorObj (X Y : C) : op (X otimes Y) = op X otimes op Y := rfl
/--
lemma `unop_tensorObj` / 引理 `unop_tensorObj`

English:
lemma unop_tensorObj
  given: (X Y : Cᵒᵖ)
  statement: unop (X otimes Y) = unop X otimes unop Y
  proof: rfl

中文:
引理 unop_tensorObj
  条件: (X Y : Cᵒᵖ)
  结论: unop (X otimes Y) = unop X otimes unop Y
  证明: rfl
-/
@[simp] lemma unop_tensorObj (X Y : Cᵒᵖ) : unop (X otimes Y) = unop X otimes unop Y := rfl

/--
lemma `op_tensorUnit` / 引理 `op_tensorUnit`

English:
lemma op_tensorUnit
  statement: op (𝟙_ C) = 𝟙_ Cᵒᵖ
  proof: rfl

中文:
引理 op_tensorUnit
  结论: op (𝟙_ C) = 𝟙_ Cᵒᵖ
  证明: rfl
-/
@[simp] lemma op_tensorUnit : op (𝟙_ C) = 𝟙_ Cᵒᵖ := rfl
/--
lemma `unop_tensorUnit` / 引理 `unop_tensorUnit`

English:
lemma unop_tensorUnit
  statement: unop (𝟙_ Cᵒᵖ) = 𝟙_ C
  proof: rfl

中文:
引理 unop_tensorUnit
  结论: unop (𝟙_ Cᵒᵖ) = 𝟙_ C
  证明: rfl
-/
@[simp] lemma unop_tensorUnit : unop (𝟙_ Cᵒᵖ) = 𝟙_ C := rfl

/--
lemma `op_tensorHom` / 引理 `op_tensorHom`

English:
lemma op_tensorHom
  given: {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  proof: rfl

中文:
引理 op_tensorHom
  条件: {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  证明: rfl
-/
@[simp] lemma op_tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f otimesₘ g).op = f.op otimesₘ g.op := rfl
/--
lemma `unop_tensorHom` / 引理 `unop_tensorHom`

English:
lemma unop_tensorHom
  given: {X₁ Y₁ X₂ Y₂ : Cᵒᵖ} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  proof: rfl

中文:
引理 unop_tensorHom
  条件: {X₁ Y₁ X₂ Y₂ : Cᵒᵖ} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  证明: rfl
-/
@[simp] lemma unop_tensorHom {X₁ Y₁ X₂ Y₂ : Cᵒᵖ} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f otimesₘ g).unop = f.unop otimesₘ g.unop := rfl

/--
lemma `op_whiskerLeft` / 引理 `op_whiskerLeft`

English:
lemma op_whiskerLeft
  given: (X : C) {Y Z : C} (f : Y ⟶ Z)
  proof: rfl

中文:
引理 op_whiskerLeft
  条件: (X : C) {Y Z : C} (f : Y ⟶ Z)
  证明: rfl
-/
@[simp] lemma op_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) :
    (X ◁ f).op = op X ◁ f.op := rfl
/--
lemma `unop_whiskerLeft` / 引理 `unop_whiskerLeft`

English:
lemma unop_whiskerLeft
  given: (X : Cᵒᵖ) {Y Z : Cᵒᵖ} (f : Y ⟶ Z)
  proof: rfl

中文:
引理 unop_whiskerLeft
  条件: (X : Cᵒᵖ) {Y Z : Cᵒᵖ} (f : Y ⟶ Z)
  证明: rfl
-/
@[simp] lemma unop_whiskerLeft (X : Cᵒᵖ) {Y Z : Cᵒᵖ} (f : Y ⟶ Z) :
    (X ◁ f).unop = unop X ◁ f.unop := rfl

/--
lemma `op_whiskerRight` / 引理 `op_whiskerRight`

English:
lemma op_whiskerRight
  given: {X Y : C} (f : X ⟶ Y) (Z : C)
  proof: rfl

中文:
引理 op_whiskerRight
  条件: {X Y : C} (f : X ⟶ Y) (Z : C)
  证明: rfl
-/
@[simp] lemma op_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    (f ▷ Z).op = f.op ▷ op Z := rfl
/--
lemma `unop_whiskerRight` / 引理 `unop_whiskerRight`

English:
lemma unop_whiskerRight
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y) (Z : Cᵒᵖ)
  proof: rfl

中文:
引理 unop_whiskerRight
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y) (Z : Cᵒᵖ)
  证明: rfl
-/
@[simp] lemma unop_whiskerRight {X Y : Cᵒᵖ} (f : X ⟶ Y) (Z : Cᵒᵖ) :
    (f ▷ Z).unop = f.unop ▷ unop Z := rfl

/--
lemma `op_associator` / 引理 `op_associator`

English:
lemma op_associator
  given: (X Y Z : C)
  proof: rfl

中文:
引理 op_associator
  条件: (X Y Z : C)
  证明: rfl
-/
@[simp] lemma op_associator (X Y Z : C) :
    (α_ X Y Z).op = (α_ (op X) (op Y) (op Z)).symm := rfl
/--
lemma `unop_associator` / 引理 `unop_associator`

English:
lemma unop_associator
  given: (X Y Z : Cᵒᵖ)
  proof: rfl

中文:
引理 unop_associator
  条件: (X Y Z : Cᵒᵖ)
  证明: rfl
-/
@[simp] lemma unop_associator (X Y Z : Cᵒᵖ) :
    (α_ X Y Z).unop = (α_ (unop X) (unop Y) (unop Z)).symm := rfl

/--
lemma `op_hom_associator` / 引理 `op_hom_associator`

English:
lemma op_hom_associator
  given: (X Y Z : C)
  proof: rfl

中文:
引理 op_hom_associator
  条件: (X Y Z : C)
  证明: rfl
-/
@[simp] lemma op_hom_associator (X Y Z : C) :
    (α_ X Y Z).hom.op = (α_ (op X) (op Y) (op Z)).inv := rfl
/--
lemma `unop_hom_associator` / 引理 `unop_hom_associator`

English:
lemma unop_hom_associator
  given: (X Y Z : Cᵒᵖ)
  proof: rfl

中文:
引理 unop_hom_associator
  条件: (X Y Z : Cᵒᵖ)
  证明: rfl
-/
@[simp] lemma unop_hom_associator (X Y Z : Cᵒᵖ) :
    (α_ X Y Z).hom.unop = (α_ (unop X) (unop Y) (unop Z)).inv := rfl

/--
lemma `op_inv_associator` / 引理 `op_inv_associator`

English:
lemma op_inv_associator
  given: (X Y Z : C)
  proof: rfl

中文:
引理 op_inv_associator
  条件: (X Y Z : C)
  证明: rfl
-/
@[simp] lemma op_inv_associator (X Y Z : C) :
    (α_ X Y Z).inv.op = (α_ (op X) (op Y) (op Z)).hom := rfl
/--
lemma `unop_inv_associator` / 引理 `unop_inv_associator`

English:
lemma unop_inv_associator
  given: (X Y Z : Cᵒᵖ)
  proof: rfl

中文:
引理 unop_inv_associator
  条件: (X Y Z : Cᵒᵖ)
  证明: rfl
-/
@[simp] lemma unop_inv_associator (X Y Z : Cᵒᵖ) :
    (α_ X Y Z).inv.unop = (α_ (unop X) (unop Y) (unop Z)).hom := rfl

/--
lemma `op_leftUnitor` / 引理 `op_leftUnitor`

English:
lemma op_leftUnitor
  given: (X : C)
  statement: (fun_ X).op = (fun_ (op X)).symm
  proof: rfl

中文:
引理 op_leftUnitor
  条件: (X : C)
  结论: (fun_ X).op = (fun_ (op X)).symm
  证明: rfl
-/
@[simp] lemma op_leftUnitor (X : C) : (fun_ X).op = (fun_ (op X)).symm := rfl
/--
lemma `unop_leftUnitor` / 引理 `unop_leftUnitor`

English:
lemma unop_leftUnitor
  given: (X : Cᵒᵖ)
  statement: (fun_ X).unop = (fun_ (unop X)).symm
  proof: rfl

中文:
引理 unop_leftUnitor
  条件: (X : Cᵒᵖ)
  结论: (fun_ X).unop = (fun_ (unop X)).symm
  证明: rfl
-/
@[simp] lemma unop_leftUnitor (X : Cᵒᵖ) : (fun_ X).unop = (fun_ (unop X)).symm := rfl

/--
lemma `op_hom_leftUnitor` / 引理 `op_hom_leftUnitor`

English:
lemma op_hom_leftUnitor
  given: (X : C)
  statement: (fun_ X).hom.op = (fun_ (op X)).inv
  proof: rfl

中文:
引理 op_hom_leftUnitor
  条件: (X : C)
  结论: (fun_ X).hom.op = (fun_ (op X)).inv
  证明: rfl
-/
@[simp] lemma op_hom_leftUnitor (X : C) : (fun_ X).hom.op = (fun_ (op X)).inv := rfl
/--
lemma `unop_hom_leftUnitor` / 引理 `unop_hom_leftUnitor`

English:
lemma unop_hom_leftUnitor
  given: (X : Cᵒᵖ)
  statement: (fun_ X).hom.unop = (fun_ (unop X)).inv
  proof: rfl

中文:
引理 unop_hom_leftUnitor
  条件: (X : Cᵒᵖ)
  结论: (fun_ X).hom.unop = (fun_ (unop X)).inv
  证明: rfl
-/
@[simp] lemma unop_hom_leftUnitor (X : Cᵒᵖ) : (fun_ X).hom.unop = (fun_ (unop X)).inv := rfl

/--
lemma `op_inv_leftUnitor` / 引理 `op_inv_leftUnitor`

English:
lemma op_inv_leftUnitor
  given: (X : C)
  statement: (fun_ X).inv.op = (fun_ (op X)).hom
  proof: rfl

中文:
引理 op_inv_leftUnitor
  条件: (X : C)
  结论: (fun_ X).inv.op = (fun_ (op X)).hom
  证明: rfl
-/
@[simp] lemma op_inv_leftUnitor (X : C) : (fun_ X).inv.op = (fun_ (op X)).hom := rfl
/--
lemma `unop_inv_leftUnitor` / 引理 `unop_inv_leftUnitor`

English:
lemma unop_inv_leftUnitor
  given: (X : Cᵒᵖ)
  statement: (fun_ X).inv.unop = (fun_ (unop X)).hom
  proof: rfl

中文:
引理 unop_inv_leftUnitor
  条件: (X : Cᵒᵖ)
  结论: (fun_ X).inv.unop = (fun_ (unop X)).hom
  证明: rfl
-/
@[simp] lemma unop_inv_leftUnitor (X : Cᵒᵖ) : (fun_ X).inv.unop = (fun_ (unop X)).hom := rfl

/--
lemma `op_rightUnitor` / 引理 `op_rightUnitor`

English:
lemma op_rightUnitor
  given: (X : C)
  statement: (ρ_ X).op = (ρ_ (op X)).symm
  proof: rfl

中文:
引理 op_rightUnitor
  条件: (X : C)
  结论: (ρ_ X).op = (ρ_ (op X)).symm
  证明: rfl
-/
@[simp] lemma op_rightUnitor (X : C) : (ρ_ X).op = (ρ_ (op X)).symm := rfl
/--
lemma `unop_rightUnitor` / 引理 `unop_rightUnitor`

English:
lemma unop_rightUnitor
  given: (X : Cᵒᵖ)
  statement: (ρ_ X).unop = (ρ_ (unop X)).symm
  proof: rfl

中文:
引理 unop_rightUnitor
  条件: (X : Cᵒᵖ)
  结论: (ρ_ X).unop = (ρ_ (unop X)).symm
  证明: rfl
-/
@[simp] lemma unop_rightUnitor (X : Cᵒᵖ) : (ρ_ X).unop = (ρ_ (unop X)).symm := rfl

/--
lemma `op_hom_rightUnitor` / 引理 `op_hom_rightUnitor`

English:
lemma op_hom_rightUnitor
  given: (X : C)
  statement: (ρ_ X).hom.op = (ρ_ (op X)).inv
  proof: rfl

中文:
引理 op_hom_rightUnitor
  条件: (X : C)
  结论: (ρ_ X).hom.op = (ρ_ (op X)).inv
  证明: rfl
-/
@[simp] lemma op_hom_rightUnitor (X : C) : (ρ_ X).hom.op = (ρ_ (op X)).inv := rfl
/--
lemma `unop_hom_rightUnitor` / 引理 `unop_hom_rightUnitor`

English:
lemma unop_hom_rightUnitor
  given: (X : Cᵒᵖ)
  statement: (ρ_ X).hom.unop = (ρ_ (unop X)).inv
  proof: rfl

中文:
引理 unop_hom_rightUnitor
  条件: (X : Cᵒᵖ)
  结论: (ρ_ X).hom.unop = (ρ_ (unop X)).inv
  证明: rfl
-/
@[simp] lemma unop_hom_rightUnitor (X : Cᵒᵖ) : (ρ_ X).hom.unop = (ρ_ (unop X)).inv := rfl

/--
lemma `op_inv_rightUnitor` / 引理 `op_inv_rightUnitor`

English:
lemma op_inv_rightUnitor
  given: (X : C)
  statement: (ρ_ X).inv.op = (ρ_ (op X)).hom
  proof: rfl

中文:
引理 op_inv_rightUnitor
  条件: (X : C)
  结论: (ρ_ X).inv.op = (ρ_ (op X)).hom
  证明: rfl
-/
@[simp] lemma op_inv_rightUnitor (X : C) : (ρ_ X).inv.op = (ρ_ (op X)).hom := rfl
/--
lemma `unop_inv_rightUnitor` / 引理 `unop_inv_rightUnitor`

English:
lemma unop_inv_rightUnitor
  given: (X : Cᵒᵖ)
  statement: (ρ_ X).inv.unop = (ρ_ (unop X)).hom
  proof: rfl

中文:
引理 unop_inv_rightUnitor
  条件: (X : Cᵒᵖ)
  结论: (ρ_ X).inv.unop = (ρ_ (unop X)).hom
  证明: rfl
-/
@[simp] lemma unop_inv_rightUnitor (X : Cᵒᵖ) : (ρ_ X).inv.unop = (ρ_ (unop X)).hom := rfl

end OppositeLemmas

/--
theorem `op_tensor_op` / 定理 `op_tensor_op`

English:
theorem op_tensor_op
  given: {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z)
  statement: f.op otimesₘ g.op = (f otimesₘ g).op
  proof: rfl

中文:
定理 op_tensor_op
  条件: {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z)
  结论: f.op otimesₘ g.op = (f otimesₘ g).op
  证明: rfl
-/
theorem op_tensor_op {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f.op otimesₘ g.op = (f otimesₘ g).op := rfl

/--
theorem `unop_tensor_unop` / 定理 `unop_tensor_unop`

English:
theorem unop_tensor_unop
  given: {W X Y Z : Cᵒᵖ} (f : W ⟶ X) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 unop_tensor_unop
  条件: {W X Y Z : Cᵒᵖ} (f : W ⟶ X) (g : Y ⟶ Z)
  证明: rfl
-/
theorem unop_tensor_unop {W X Y Z : Cᵒᵖ} (f : W ⟶ X) (g : Y ⟶ Z) :
    f.unop otimesₘ g.unop = (f otimesₘ g).unop := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `monoidalCategoryMop` / 实例 `monoidalCategoryMop`

English:
instance monoidalCategoryMop
  signature: : MonoidalCategory Cᴹᵒᵖ where
  body: mop (unmop Y otimes unmop X)
  whiskerLeft X _ _ f := (f.unmop ▷ X.unmop).mop
  whiskerRight f X := (X.unmop ◁ f.unmop).mop
  tensorHom f g := (g.unmop otimesₘ f.unmop).mop
  tensorHom_def _ _ := Quiver.Hom.unmop_inj (tensorHom_def' _ _)
tensorHom_comp_tensorHom _ _ _ _ := Quiver.Hom.unmop_inj by si

中文:
实例 monoidalCategoryMop
  签名: : MonoidalCategory Cᴹᵒᵖ where
  定义体: mop (unmop Y otimes unmop X)
  whiskerLeft X _ _ f := (f.unmop ▷ X.unmop).mop
  whiskerRight f X := (X.unmop ◁ f.unmop).mop
  tensorHom f g := (g.unmop otimesₘ f.unmop).mop
  tensorHom_def _ _ := Quiver.Hom.unmop_inj (tensorHom_def' _ _)
tensorHom_comp_tensorHom _ _ _ _ := Quiver.Hom.unmop_inj by si

Depends on / 依赖: otimes
-/
instance monoidalCategoryMop : MonoidalCategory Cᴹᵒᵖ where
  tensorObj X Y := mop (unmop Y otimes unmop X)
  whiskerLeft X _ _ f := (f.unmop ▷ X.unmop).mop
  whiskerRight f X := (X.unmop ◁ f.unmop).mop
  tensorHom f g := (g.unmop otimesₘ f.unmop).mop
  tensorHom_def _ _ := Quiver.Hom.unmop_inj (tensorHom_def' _ _)
tensorHom_comp_tensorHom _ _ _ _ := Quiver.Hom.unmop_inj by simp
  tensorUnit := mop (𝟙_ C)
  associator X Y Z := (α_ (unmop Z) (unmop Y) (unmop X)).symm.mop
  leftUnitor X := (ρ_ (unmop X)).mop
  rightUnitor X := (fun_ (unmop X)).mop
associator_naturality f g h := Quiver.Hom.unmop_inj by simp
leftUnitor_naturality f := Quiver.Hom.unmop_inj by simp
rightUnitor_naturality f := Quiver.Hom.unmop_inj by simp
triangle X Y := Quiver.Hom.unmop_inj by dsimp; monoidal_coherence
pentagon W X Y Z := Quiver.Hom.unmop_inj by dsimp; monoidal_coherence

-- it would be nice if we could autogenerate all of these somehow
section MonoidalOppositeLemmas

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_tensorObj` / 引理 `mop_tensorObj`

English:
lemma mop_tensorObj
  given: (X Y : C)
  statement: mop (X otimes Y) = mop Y otimes mop X
  proof: rfl

中文:
引理 mop_tensorObj
  条件: (X Y : C)
  结论: mop (X otimes Y) = mop Y otimes mop X
  证明: rfl
-/
@[simp] lemma mop_tensorObj (X Y : C) : mop (X otimes Y) = mop Y otimes mop X := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_tensorObj` / 引理 `unmop_tensorObj`

English:
lemma unmop_tensorObj
  given: (X Y : Cᴹᵒᵖ)
  statement: unmop (X otimes Y) = unmop Y otimes unmop X
  proof: rfl

中文:
引理 unmop_tensorObj
  条件: (X Y : Cᴹᵒᵖ)
  结论: unmop (X otimes Y) = unmop Y otimes unmop X
  证明: rfl
-/
@[simp] lemma unmop_tensorObj (X Y : Cᴹᵒᵖ) : unmop (X otimes Y) = unmop Y otimes unmop X := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_tensorUnit` / 引理 `mop_tensorUnit`

English:
lemma mop_tensorUnit
  statement: mop (𝟙_ C) = 𝟙_ Cᴹᵒᵖ
  proof: rfl

中文:
引理 mop_tensorUnit
  结论: mop (𝟙_ C) = 𝟙_ Cᴹᵒᵖ
  证明: rfl
-/
@[simp] lemma mop_tensorUnit : mop (𝟙_ C) = 𝟙_ Cᴹᵒᵖ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_tensorUnit` / 引理 `unmop_tensorUnit`

English:
lemma unmop_tensorUnit
  statement: unmop (𝟙_ Cᴹᵒᵖ) = 𝟙_ C
  proof: rfl

中文:
引理 unmop_tensorUnit
  结论: unmop (𝟙_ Cᴹᵒᵖ) = 𝟙_ C
  证明: rfl
-/
@[simp] lemma unmop_tensorUnit : unmop (𝟙_ Cᴹᵒᵖ) = 𝟙_ C := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_tensorHom` / 引理 `mop_tensorHom`

English:
lemma mop_tensorHom
  given: {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  proof: rfl

中文:
引理 mop_tensorHom
  条件: {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  证明: rfl
-/
@[simp] lemma mop_tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f otimesₘ g).mop = g.mop otimesₘ f.mop := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_tensorHom` / 引理 `unmop_tensorHom`

English:
lemma unmop_tensorHom
  given: {X₁ Y₁ X₂ Y₂ : Cᴹᵒᵖ} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  proof: rfl

中文:
引理 unmop_tensorHom
  条件: {X₁ Y₁ X₂ Y₂ : Cᴹᵒᵖ} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  证明: rfl
-/
@[simp] lemma unmop_tensorHom {X₁ Y₁ X₂ Y₂ : Cᴹᵒᵖ} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f otimesₘ g).unmop = g.unmop otimesₘ f.unmop := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_whiskerLeft` / 引理 `mop_whiskerLeft`

English:
lemma mop_whiskerLeft
  given: (X : C) {Y Z : C} (f : Y ⟶ Z)
  proof: rfl

中文:
引理 mop_whiskerLeft
  条件: (X : C) {Y Z : C} (f : Y ⟶ Z)
  证明: rfl
-/
@[simp] lemma mop_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) :
    (X ◁ f).mop = f.mop ▷ mop X := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_whiskerLeft` / 引理 `unmop_whiskerLeft`

English:
lemma unmop_whiskerLeft
  given: (X : Cᴹᵒᵖ) {Y Z : Cᴹᵒᵖ} (f : Y ⟶ Z)
  proof: rfl

中文:
引理 unmop_whiskerLeft
  条件: (X : Cᴹᵒᵖ) {Y Z : Cᴹᵒᵖ} (f : Y ⟶ Z)
  证明: rfl
-/
@[simp] lemma unmop_whiskerLeft (X : Cᴹᵒᵖ) {Y Z : Cᴹᵒᵖ} (f : Y ⟶ Z) :
    (X ◁ f).unmop = f.unmop ▷ unmop X := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_whiskerRight` / 引理 `mop_whiskerRight`

English:
lemma mop_whiskerRight
  given: {X Y : C} (f : X ⟶ Y) (Z : C)
  proof: rfl

中文:
引理 mop_whiskerRight
  条件: {X Y : C} (f : X ⟶ Y) (Z : C)
  证明: rfl
-/
@[simp] lemma mop_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    (f ▷ Z).mop = mop Z ◁ f.mop := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_whiskerRight` / 引理 `unmop_whiskerRight`

English:
lemma unmop_whiskerRight
  given: {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) (Z : Cᴹᵒᵖ)
  proof: rfl

中文:
引理 unmop_whiskerRight
  条件: {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) (Z : Cᴹᵒᵖ)
  证明: rfl

Depends on / 依赖: Subtype, Subtype.val
-/
@[simp] lemma unmop_whiskerRight {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) (Z : Cᴹᵒᵖ) :
    (f ▷ Z).unmop = unmop Z ◁ f.unmop := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_associator` / 引理 `mop_associator`

English:
lemma mop_associator
  given: (X Y Z : C)
  proof: rfl

中文:
引理 mop_associator
  条件: (X Y Z : C)
  证明: rfl
-/
@[simp] lemma mop_associator (X Y Z : C) :
    (α_ X Y Z).mop = (α_ (mop Z) (mop Y) (mop X)).symm := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_associator` / 引理 `unmop_associator`

English:
lemma unmop_associator
  given: (X Y Z : Cᴹᵒᵖ)
  proof: rfl

中文:
引理 unmop_associator
  条件: (X Y Z : Cᴹᵒᵖ)
  证明: rfl
-/
@[simp] lemma unmop_associator (X Y Z : Cᴹᵒᵖ) :
    (α_ X Y Z).unmop = (α_ (unmop Z) (unmop Y) (unmop X)).symm := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_hom_associator` / 引理 `mop_hom_associator`

English:
lemma mop_hom_associator
  given: (X Y Z : C)
  proof: rfl

中文:
引理 mop_hom_associator
  条件: (X Y Z : C)
  证明: rfl
-/
@[simp] lemma mop_hom_associator (X Y Z : C) :
    (α_ X Y Z).hom.mop = (α_ (mop Z) (mop Y) (mop X)).inv := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_hom_associator` / 引理 `unmop_hom_associator`

English:
lemma unmop_hom_associator
  given: (X Y Z : Cᴹᵒᵖ)
  proof: rfl

中文:
引理 unmop_hom_associator
  条件: (X Y Z : Cᴹᵒᵖ)
  证明: rfl
-/
@[simp] lemma unmop_hom_associator (X Y Z : Cᴹᵒᵖ) :
    (α_ X Y Z).hom.unmop = (α_ (unmop Z) (unmop Y) (unmop X)).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_inv_associator` / 引理 `mop_inv_associator`

English:
lemma mop_inv_associator
  given: (X Y Z : C)
  proof: rfl

中文:
引理 mop_inv_associator
  条件: (X Y Z : C)
  证明: rfl
-/
@[simp] lemma mop_inv_associator (X Y Z : C) :
    (α_ X Y Z).inv.mop = (α_ (mop Z) (mop Y) (mop X)).hom := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_inv_associator` / 引理 `unmop_inv_associator`

English:
lemma unmop_inv_associator
  given: (X Y Z : Cᴹᵒᵖ)
  proof: rfl

中文:
引理 unmop_inv_associator
  条件: (X Y Z : Cᴹᵒᵖ)
  证明: rfl
-/
@[simp] lemma unmop_inv_associator (X Y Z : Cᴹᵒᵖ) :
    (α_ X Y Z).inv.unmop = (α_ (unmop Z) (unmop Y) (unmop X)).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_leftUnitor` / 引理 `mop_leftUnitor`

English:
lemma mop_leftUnitor
  given: (X : C)
  statement: (fun_ X).mop = (ρ_ (mop X))
  proof: rfl

中文:
引理 mop_leftUnitor
  条件: (X : C)
  结论: (fun_ X).mop = (ρ_ (mop X))
  证明: rfl
-/
@[simp] lemma mop_leftUnitor (X : C) : (fun_ X).mop = (ρ_ (mop X)) := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_leftUnitor` / 引理 `unmop_leftUnitor`

English:
lemma unmop_leftUnitor
  given: (X : Cᴹᵒᵖ)
  statement: (fun_ X).unmop = ρ_ (unmop X)
  proof: rfl

中文:
引理 unmop_leftUnitor
  条件: (X : Cᴹᵒᵖ)
  结论: (fun_ X).unmop = ρ_ (unmop X)
  证明: rfl
-/
@[simp] lemma unmop_leftUnitor (X : Cᴹᵒᵖ) : (fun_ X).unmop = ρ_ (unmop X) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_hom_leftUnitor` / 引理 `mop_hom_leftUnitor`

English:
lemma mop_hom_leftUnitor
  given: (X : C)
  statement: (fun_ X).hom.mop = (ρ_ (mop X)).hom
  proof: rfl

中文:
引理 mop_hom_leftUnitor
  条件: (X : C)
  结论: (fun_ X).hom.mop = (ρ_ (mop X)).hom
  证明: rfl
-/
@[simp] lemma mop_hom_leftUnitor (X : C) : (fun_ X).hom.mop = (ρ_ (mop X)).hom := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_hom_leftUnitor` / 引理 `unmop_hom_leftUnitor`

English:
lemma unmop_hom_leftUnitor
  given: (X : Cᴹᵒᵖ)
  statement: (fun_ X).hom.unmop = (ρ_ (unmop X)).hom
  proof: rfl

中文:
引理 unmop_hom_leftUnitor
  条件: (X : Cᴹᵒᵖ)
  结论: (fun_ X).hom.unmop = (ρ_ (unmop X)).hom
  证明: rfl
-/
@[simp] lemma unmop_hom_leftUnitor (X : Cᴹᵒᵖ) : (fun_ X).hom.unmop = (ρ_ (unmop X)).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_inv_leftUnitor` / 引理 `mop_inv_leftUnitor`

English:
lemma mop_inv_leftUnitor
  given: (X : C)
  statement: (fun_ X).inv.mop = (ρ_ (mop X)).inv
  proof: rfl

中文:
引理 mop_inv_leftUnitor
  条件: (X : C)
  结论: (fun_ X).inv.mop = (ρ_ (mop X)).inv
  证明: rfl
-/
@[simp] lemma mop_inv_leftUnitor (X : C) : (fun_ X).inv.mop = (ρ_ (mop X)).inv := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_inv_leftUnitor` / 引理 `unmop_inv_leftUnitor`

English:
lemma unmop_inv_leftUnitor
  given: (X : Cᴹᵒᵖ)
  statement: (fun_ X).inv.unmop = (ρ_ (unmop X)).inv
  proof: rfl

中文:
引理 unmop_inv_leftUnitor
  条件: (X : Cᴹᵒᵖ)
  结论: (fun_ X).inv.unmop = (ρ_ (unmop X)).inv
  证明: rfl
-/
@[simp] lemma unmop_inv_leftUnitor (X : Cᴹᵒᵖ) : (fun_ X).inv.unmop = (ρ_ (unmop X)).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_rightUnitor` / 引理 `mop_rightUnitor`

English:
lemma mop_rightUnitor
  given: (X : C)
  statement: (ρ_ X).mop = (fun_ (mop X))
  proof: rfl

中文:
引理 mop_rightUnitor
  条件: (X : C)
  结论: (ρ_ X).mop = (fun_ (mop X))
  证明: rfl
-/
@[simp] lemma mop_rightUnitor (X : C) : (ρ_ X).mop = (fun_ (mop X)) := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_rightUnitor` / 引理 `unmop_rightUnitor`

English:
lemma unmop_rightUnitor
  given: (X : Cᴹᵒᵖ)
  statement: (ρ_ X).unmop = fun_ (unmop X)
  proof: rfl

中文:
引理 unmop_rightUnitor
  条件: (X : Cᴹᵒᵖ)
  结论: (ρ_ X).unmop = fun_ (unmop X)
  证明: rfl
-/
@[simp] lemma unmop_rightUnitor (X : Cᴹᵒᵖ) : (ρ_ X).unmop = fun_ (unmop X) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_hom_rightUnitor` / 引理 `mop_hom_rightUnitor`

English:
lemma mop_hom_rightUnitor
  given: (X : C)
  statement: (ρ_ X).hom.mop = (fun_ (mop X)).hom
  proof: rfl

中文:
引理 mop_hom_rightUnitor
  条件: (X : C)
  结论: (ρ_ X).hom.mop = (fun_ (mop X)).hom
  证明: rfl
-/
@[simp] lemma mop_hom_rightUnitor (X : C) : (ρ_ X).hom.mop = (fun_ (mop X)).hom := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_hom_rightUnitor` / 引理 `unmop_hom_rightUnitor`

English:
lemma unmop_hom_rightUnitor
  given: (X : Cᴹᵒᵖ)
  statement: (ρ_ X).hom.unmop = (fun_ (unmop X)).hom
  proof: rfl

中文:
引理 unmop_hom_rightUnitor
  条件: (X : Cᴹᵒᵖ)
  结论: (ρ_ X).hom.unmop = (fun_ (unmop X)).hom
  证明: rfl
-/
@[simp] lemma unmop_hom_rightUnitor (X : Cᴹᵒᵖ) : (ρ_ X).hom.unmop = (fun_ (unmop X)).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mop_inv_rightUnitor` / 引理 `mop_inv_rightUnitor`

English:
lemma mop_inv_rightUnitor
  given: (X : C)
  statement: (ρ_ X).inv.mop = (fun_ (mop X)).inv
  proof: rfl

中文:
引理 mop_inv_rightUnitor
  条件: (X : C)
  结论: (ρ_ X).inv.mop = (fun_ (mop X)).inv
  证明: rfl
-/
@[simp] lemma mop_inv_rightUnitor (X : C) : (ρ_ X).inv.mop = (fun_ (mop X)).inv := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unmop_inv_rightUnitor` / 引理 `unmop_inv_rightUnitor`

English:
lemma unmop_inv_rightUnitor
  given: (X : Cᴹᵒᵖ)
  statement: (ρ_ X).inv.unmop = (fun_ (unmop X)).inv
  proof: rfl

中文:
引理 unmop_inv_rightUnitor
  条件: (X : Cᴹᵒᵖ)
  结论: (ρ_ X).inv.unmop = (fun_ (unmop X)).inv
  证明: rfl
-/
@[simp] lemma unmop_inv_rightUnitor (X : Cᴹᵒᵖ) : (ρ_ X).inv.unmop = (fun_ (unmop X)).inv := rfl

end MonoidalOppositeLemmas

variable (C)

set_option backward.defeqAttrib.useBackward true in
set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `MonoidalOpposite.mopEquiv` / `MonoidalOpposite.mopEquiv` 的定义

English:
definition MonoidalOpposite.mopEquiv
  signature: : C ≌ Cᴹᵒᵖ where
  body: mopFunctor C
  inverse := unmopFunctor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 MonoidalOpposite.mopEquiv
  签名: : C ≌ Cᴹᵒᵖ where
  定义体: mopFunctor C
  inverse := unmopFunctor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _
-/
@[simps] def MonoidalOpposite.mopEquiv : C ≌ Cᴹᵒᵖ where
  functor := mopFunctor C
  inverse := unmopFunctor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/--
Definition of `MonoidalOpposite.unmopEquiv` / `MonoidalOpposite.unmopEquiv` 的定义

English:
definition MonoidalOpposite.unmopEquiv
  signature: : Cᴹᵒᵖ ≌ C
  body: (mopEquiv C).symm

#adaptation_note

中文:
定义 MonoidalOpposite.unmopEquiv
  签名: : Cᴹᵒᵖ ≌ C
  定义体: (mopEquiv C).symm

#adaptation_note
-/
@[simps!] def MonoidalOpposite.unmopEquiv : Cᴹᵒᵖ ≌ C := (mopEquiv C).symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `MonoidalOpposite.mopMopEquivalence` / `MonoidalOpposite.mopMopEquivalence` 的定义

English:
definition MonoidalOpposite.mopMopEquivalence
  signature: : Cᴹᵒᵖᴹᵒᵖ ≌ C
  body: .trans (MonoidalOpposite.unmopEquiv Cᴹᵒᵖ) (MonoidalOpposite.unmopEquiv C)

中文:
定义 MonoidalOpposite.mopMopEquivalence
  签名: : Cᴹᵒᵖᴹᵒᵖ ≌ C
  定义体: .trans (MonoidalOpposite.unmopEquiv Cᴹᵒᵖ) (MonoidalOpposite.unmopEquiv C)
-/
@[simps!] def MonoidalOpposite.mopMopEquivalence : Cᴹᵒᵖᴹᵒᵖ ≌ C :=
  .trans (MonoidalOpposite.unmopEquiv Cᴹᵒᵖ) (MonoidalOpposite.unmopEquiv C)

set_option backward.isDefEq.respectTransparency.types false in
@[simps!]
/--
Instance `MonoidalOpposite.mopMopEquivalenceFunctorMonoidal` / 实例 `MonoidalOpposite.mopMopEquivalenceFunctorMonoidal`

English:
instance MonoidalOpposite.mopMopEquivalenceFunctorMonoidal
  signature: :
  body: 𝟙 _
  δ X Y := 𝟙 _
  μ X Y := 𝟙 _
  η := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _

中文:
实例 MonoidalOpposite.mopMopEquivalenceFunctorMonoidal
  签名: :
  定义体: 𝟙 _
  δ X Y := 𝟙 _
  μ X Y := 𝟙 _
  η := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _
-/
instance MonoidalOpposite.mopMopEquivalenceFunctorMonoidal :
    (MonoidalOpposite.mopMopEquivalence C).functor.Monoidal where
  ε := 𝟙 _
  δ X Y := 𝟙 _
  μ X Y := 𝟙 _
  η := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
@[simps!]
/--
Instance `MonoidalOpposite.mopMopEquivalenceInverseMonoidal` / 实例 `MonoidalOpposite.mopMopEquivalenceInverseMonoidal`

English:
instance MonoidalOpposite.mopMopEquivalenceInverseMonoidal
  signature: :
  body: 𝟙 _
  δ X Y := 𝟙 _
  μ X Y := 𝟙 _
  η := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _

中文:
实例 MonoidalOpposite.mopMopEquivalenceInverseMonoidal
  签名: :
  定义体: 𝟙 _
  δ X Y := 𝟙 _
  μ X Y := 𝟙 _
  η := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _
-/
instance MonoidalOpposite.mopMopEquivalenceInverseMonoidal :
    (MonoidalOpposite.mopMopEquivalence C).inverse.Monoidal where
  ε := 𝟙 _
  δ X Y := 𝟙 _
  μ X Y := 𝟙 _
  η := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (mopMopEquivalence C).IsMonoidal
  body: by
    simp [ε, η, mopMopEquivalence, Equivalence.trans, unmopEquiv, ε]
  leftAdjoint_μ X Y := by
    simp [μ, δ, mopMopEquivalence, Equivalence.trans, unmopEquiv, μ]

中文:
实例 :
  签名: (mopMopEquivalence C).IsMonoidal
  定义体: by
    simp [ε, η, mopMopEquivalence, Equivalence.trans, unmopEquiv, ε]
  leftAdjoint_μ X Y := by
    simp [μ, δ, mopMopEquivalence, Equivalence.trans, unmopEquiv, μ]

Depends on / 依赖: Equivalence, Equivalence.trans, mopMopEquivalence, unmopEquiv
-/
instance : (mopMopEquivalence C).IsMonoidal where
  leftAdjoint_ε := by
    simp [ε, η, mopMopEquivalence, Equivalence.trans, unmopEquiv, ε]
  leftAdjoint_μ X Y := by
    simp [μ, δ, mopMopEquivalence, Equivalence.trans, unmopEquiv, μ]

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `mop X ⊗ mop Y = mop (Y ⊗ X)` as a natural isomorphism. -/
@[simps!]
/--
Definition of `MonoidalOpposite.tensorIso` / `MonoidalOpposite.tensorIso` 的定义

English:
definition MonoidalOpposite.tensorIso
  signature: :
  body: Iso.refl _

中文:
定义 MonoidalOpposite.tensorIso
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def MonoidalOpposite.tensorIso :
    tensor Cᴹᵒᵖ ≅ (unmopFunctor C).prod (unmopFunctor C) ⋙
      Prod.swap C C ⋙ tensor C ⋙ mopFunctor C :=
  Iso.refl _

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `X ⊗ - = mop (- ⊗ unmop X)` as a natural isomorphism. -/
@[simps!]
/--
Definition of `MonoidalOpposite.tensorLeftIso` / `MonoidalOpposite.tensorLeftIso` 的定义

English:
definition MonoidalOpposite.tensorLeftIso
  signature: (X : Cᴹᵒᵖ)
  body: Iso.refl _

中文:
定义 MonoidalOpposite.tensorLeftIso
  签名: (X : Cᴹᵒᵖ)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def MonoidalOpposite.tensorLeftIso (X : Cᴹᵒᵖ) :
    tensorLeft X ≅ unmopFunctor C ⋙ tensorRight (unmop X) ⋙ mopFunctor C :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `mop X ⊗ - = mop (- ⊗ X)` as a natural isomorphism. -/
@[simps!]
/--
Definition of `MonoidalOpposite.tensorLeftMopIso` / `MonoidalOpposite.tensorLeftMopIso` 的定义

English:
definition MonoidalOpposite.tensorLeftMopIso
  signature: (X : C)
  body: Iso.refl _

中文:
定义 MonoidalOpposite.tensorLeftMopIso
  签名: (X : C)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def MonoidalOpposite.tensorLeftMopIso (X : C) :
    tensorLeft (mop X) ≅ unmopFunctor C ⋙ tensorRight X ⋙ mopFunctor C :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `unmop X ⊗ - = unmop (mop - ⊗ X)` as a natural isomorphism. -/
@[simps!]
/--
Definition of `MonoidalOpposite.tensorLeftUnmopIso` / `MonoidalOpposite.tensorLeftUnmopIso` 的定义

English:
definition MonoidalOpposite.tensorLeftUnmopIso
  signature: (X : Cᴹᵒᵖ)
  body: Iso.refl _

中文:
定义 MonoidalOpposite.tensorLeftUnmopIso
  签名: (X : Cᴹᵒᵖ)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def MonoidalOpposite.tensorLeftUnmopIso (X : Cᴹᵒᵖ) :
    tensorLeft (unmop X) ≅ mopFunctor C ⋙ tensorRight X ⋙ unmopFunctor C :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `- ⊗ X = mop (unmop X ⊗ -)` as a natural isomorphism. -/
@[simps!]
/--
Definition of `MonoidalOpposite.tensorRightIso` / `MonoidalOpposite.tensorRightIso` 的定义

English:
definition MonoidalOpposite.tensorRightIso
  signature: (X : Cᴹᵒᵖ)
  body: Iso.refl _

中文:
定义 MonoidalOpposite.tensorRightIso
  签名: (X : Cᴹᵒᵖ)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def MonoidalOpposite.tensorRightIso (X : Cᴹᵒᵖ) :
    tensorRight X ≅ unmopFunctor C ⋙ tensorLeft (unmop X) ⋙ mopFunctor C :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `- ⊗ mop X = mop (- ⊗ unmop X)` as a natural isomorphism. -/
@[simps!]
/--
Definition of `MonoidalOpposite.tensorRightMopIso` / `MonoidalOpposite.tensorRightMopIso` 的定义

English:
definition MonoidalOpposite.tensorRightMopIso
  signature: (X : C)
  body: Iso.refl _

中文:
定义 MonoidalOpposite.tensorRightMopIso
  签名: (X : C)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def MonoidalOpposite.tensorRightMopIso (X : C) :
    tensorRight (mop X) ≅ unmopFunctor C ⋙ tensorLeft X ⋙ mopFunctor C :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `- ⊗ unmop X = unmop (X ⊗ mop -)` as a natural isomorphism. -/
@[simps!]
/--
Definition of `MonoidalOpposite.tensorRightUnmopIso` / `MonoidalOpposite.tensorRightUnmopIso` 的定义

English:
definition MonoidalOpposite.tensorRightUnmopIso
  signature: (X : Cᴹᵒᵖ)
  body: Iso.refl _

@[simps]

中文:
定义 MonoidalOpposite.tensorRightUnmopIso
  签名: (X : Cᴹᵒᵖ)
  定义体: Iso.refl _

@[simps]

Depends on / 依赖: Iso.refl
-/
def MonoidalOpposite.tensorRightUnmopIso (X : Cᴹᵒᵖ) :
    tensorRight (unmop X) ≅ mopFunctor C ⋙ tensorLeft X ⋙ unmopFunctor C :=
  Iso.refl _

@[simps]
/--
Instance `monoidalOpOp` / 实例 `monoidalOpOp`

English:
instance monoidalOpOp
  signature: : (opOp C).Monoidal where
  body: 𝟙 _
  η := 𝟙 _
  μ X Y := 𝟙 _
  δ X Y := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _

@[simps]

中文:
实例 monoidalOpOp
  签名: : (opOp C).Monoidal where
  定义体: 𝟙 _
  η := 𝟙 _
  μ X Y := 𝟙 _
  δ X Y := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _

@[simps]
-/
instance monoidalOpOp : (opOp C).Monoidal where
  ε := 𝟙 _
  η := 𝟙 _
  μ X Y := 𝟙 _
  δ X Y := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _

@[simps]
/--
Instance `monoidalUnopUnop` / 实例 `monoidalUnopUnop`

English:
instance monoidalUnopUnop
  signature: : (unopUnop C).Monoidal where
  body: 𝟙 _
  η := 𝟙 _
  μ X Y := 𝟙 _
  δ X Y := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _

中文:
实例 monoidalUnopUnop
  签名: : (unopUnop C).Monoidal where
  定义体: 𝟙 _
  η := 𝟙 _
  μ X Y := 𝟙 _
  δ X Y := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _
-/
instance monoidalUnopUnop : (unopUnop C).Monoidal where
  ε := 𝟙 _
  η := 𝟙 _
  μ X Y := 𝟙 _
  δ X Y := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (opOpEquivalence C).functor.Monoidal
  body: monoidalUnopUnop

中文:
实例 :
  签名: (opOpEquivalence C).functor.Monoidal
  定义体: monoidalUnopUnop

Depends on / 依赖: monoidalUnopUnop
-/
instance : (opOpEquivalence C).functor.Monoidal := monoidalUnopUnop
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (opOpEquivalence C).inverse.Monoidal
  body: monoidalOpOp

中文:
实例 :
  签名: (opOpEquivalence C).inverse.Monoidal
  定义体: monoidalOpOp

Depends on / 依赖: choose_spec, exists_simple_subobject, monoidalOpOp
-/
instance : (opOpEquivalence C).inverse.Monoidal := monoidalOpOp

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (opOpEquivalence C).IsMonoidal
  body: by simp [opOpEquivalence]
  leftAdjoint_μ := by simp [opOpEquivalence]

中文:
实例 :
  签名: (opOpEquivalence C).IsMonoidal
  定义体: by simp [opOpEquivalence]
  leftAdjoint_μ := by simp [opOpEquivalence]

Depends on / 依赖: opOpEquivalence
-/
instance : (opOpEquivalence C).IsMonoidal where
  leftAdjoint_ε := by simp [opOpEquivalence]
  leftAdjoint_μ := by simp [opOpEquivalence]

end CategoryTheory
