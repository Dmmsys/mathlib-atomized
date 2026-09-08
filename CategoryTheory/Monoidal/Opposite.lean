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

/-- The type of objects of the opposite (or "reverse") monoidal category.
Use the notation `Cᴹᵒᵖ`. -/
/-
**CategoryTheory.MonoidalOpposite** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：Type u₁ → Type u₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of objects of the opposite (or "reverse") monoidal category.
Use the notation `Cᴹᵒᵖ`.
-/
structure MonoidalOpposite (C : Type u₁) where
  /-- The object of `MonoidalOpposite C` that represents `x : C`. -/ mop ::
  /-- The object of `C` represented by `x : MonoidalOpposite C`. -/ unmop : C

namespace MonoidalOpposite

@[inherit_doc]
notation:max C "ᴹᵒᵖ" => MonoidalOpposite C

/-
**CategoryTheory.MonoidalOpposite.mop_injective** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MonoidalOpposite`。
形式化陈述：mop_injective : Function.Injective (mop : C -> Cᴹᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalOpposite.mop.inj`：∀ {C : Type u₁} {unmop unmop_1 
: C}, { unmop := unmop } = { unmop := unmop_1 } → unmop = unmop_1
-/
theorem mop_injective : Function.Injective (mop : C → Cᴹᵒᵖ) := @mop.inj C
/-
**CategoryTheory.MonoidalOpposite.unmop_injective** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MonoidalOpposite`。
形式化陈述：unmop_injective : Function.Injective (unmop : Cᴹᵒᵖ -> C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem unmop_injective : Function.Injective (unmop : Cᴹᵒᵖ → C) :=
  fun _ _ h => congrArg mop h
/-
**CategoryTheory.MonoidalOpposite.mop_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.MonoidalOpposite`。
形式化陈述：mop_inj_iff (x y : C) : mop x = mop y ↔ x = y
参数：x y : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `CategoryTheory.MonoidalOpposite.mop_injective`：mop_injective : Function.
Injective (mop : C -> Cᴹᵒᵖ)
-/
theorem mop_inj_iff (x y : C) : mop x = mop y ↔ x = y := mop_injective.eq_iff

@[simp]
/-
**CategoryTheory.MonoidalOpposite.unmop_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MonoidalOpposite`。
形式化陈述：unmop_inj_iff (x y : Cᴹᵒᵖ) : unmop x = unmop y ↔ x = y
参数：x y : Cᴹᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `CategoryTheory.MonoidalOpposite.unmop_injective`：unmop_injective : Funct
ion.Injective (unmop : Cᴹᵒᵖ -> C)
-/
theorem unmop_inj_iff (x y : Cᴹᵒᵖ) : unmop x = unmop y ↔ x = y := unmop_injective.eq_iff

@[simp]
/-
**CategoryTheory.MonoidalOpposite.mop_unmop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.MonoidalOpposite`。
形式化陈述：mop_unmop (X : Cᴹᵒᵖ) : mop (unmop X) = X
参数：X : Cᴹᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mop_unmop (X : Cᴹᵒᵖ) : mop (unmop X) = X := rfl

-- can't be simp bc after putting the lhs in whnf it's `X = X`
/-
**CategoryTheory.MonoidalOpposite.unmop_mop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.MonoidalOpposite`。
形式化陈述：unmop_mop (X : C) : unmop (mop X) = X
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unmop_mop (X : C) : unmop (mop X) = X := rfl
/-
**CategoryTheory.MonoidalOpposite.monoidalOppositeCategory** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.MonoidalOpposite`。
形式化陈述：monoidalOppositeCategory [Category.{v₁} C] : Category Cᴹᵒᵖ where Hom X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- The monoidal opposite of a morphism `f : X ⟶ Y` is just `f`, thought of as `mop X ⟶ mop Y`. -/
/-
**Quiver.Hom.mop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quiver.Hom.mop {X Y : C} (f : X ⟶ Y) : mop X ⟶ mop Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal opposite of a morphism `f : X ⟶ Y` is just `f`, thought of as `mop 
X ⟶ mop Y`.
-/
def Quiver.Hom.mop {X Y : C} (f : X ⟶ Y) : mop X ⟶ mop Y := MonoidalOpposite.mop f

/-- We can think of a morphism `f : mop X ⟶ mop Y` as a morphism `X ⟶ Y`. -/
/-
**Quiver.Hom.unmop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quiver.Hom.unmop {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) : unmop X ⟶ unmop Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can think of a morphism `f : mop X ⟶ mop Y` as a morphism `X ⟶ Y`.
-/
def Quiver.Hom.unmop {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) : unmop X ⟶ unmop Y := MonoidalOpposite.unmop f

namespace Quiver.Hom

open MonoidalOpposite renaming mop → mop', unmop → unmop'

/-
**Quiver.Hom.mop_inj** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Hom`。
形式化陈述：mop_inj {X Y : C} : Function.Injective (Quiver.Hom.mop : (X ⟶ Y) -> (mop' 
X ⟶ mop' Y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem mop_inj {X Y : C} :
    Function.Injective (Quiver.Hom.mop : (X ⟶ Y) → (mop' X ⟶ mop' Y)) :=
  fun _ _ H => congr_arg Quiver.Hom.unmop H
/-
**Quiver.Hom.unmop_inj** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Hom`。
形式化陈述：unmop_inj {X Y : Cᴹᵒᵖ} : Function.Injective (Quiver.Hom.unmop : (X ⟶ Y) ->
 (unmop' X ⟶ unmop' Y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem unmop_inj {X Y : Cᴹᵒᵖ} :
    Function.Injective (Quiver.Hom.unmop : (X ⟶ Y) → (unmop' X ⟶ unmop' Y)) :=
  fun _ _ H => congr_arg Quiver.Hom.mop H

@[simp]
/-
**Quiver.Hom.unmop_mop** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Hom`。
形式化陈述：unmop_mop {X Y : C} {f : X ⟶ Y} : f.mop.unmop = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unmop_mop {X Y : C} {f : X ⟶ Y} : f.mop.unmop = f :=
  rfl

@[simp]
/-
**Quiver.Hom.mop_unmop** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Hom`。
形式化陈述：mop_unmop {X Y : Cᴹᵒᵖ} {f : X ⟶ Y} : f.unmop.mop = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mop_unmop {X Y : Cᴹᵒᵖ} {f : X ⟶ Y} : f.unmop.mop = f :=
  rfl

end Quiver.Hom

namespace CategoryTheory

@[simp]
/-
**CategoryTheory.mop_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：mop_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).mop = f.mop ≫ g.mop
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mop_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} :
    (f ≫ g).mop = f.mop ≫ g.mop := rfl

@[simp]
/-
**CategoryTheory.mop_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：mop_id {X : C} : (𝟙 X).mop = 𝟙 (mop X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mop_id {X : C} : (𝟙 X).mop = 𝟙 (mop X) := rfl

@[simp]
/-
**CategoryTheory.unmop_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unmop_comp {X Y Z : Cᴹᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).unmop = f.unmo
p ≫ g.unmop
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unmop_comp {X Y Z : Cᴹᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} :
    (f ≫ g).unmop = f.unmop ≫ g.unmop := rfl

@[simp]
/-
**CategoryTheory.unmop_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unmop_id {X : Cᴹᵒᵖ} : (𝟙 X).unmop = 𝟙 (unmop X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unmop_id {X : Cᴹᵒᵖ} : (𝟙 X).unmop = 𝟙 (unmop X) := rfl

@[simp]
/-
**CategoryTheory.unmop_id_mop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unmop_id_mop {X : C} : (𝟙 (mop X)).unmop = 𝟙 X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unmop_id_mop {X : C} : (𝟙 (mop X)).unmop = 𝟙 X := rfl

@[simp]
/-
**CategoryTheory.mop_id_unmop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：mop_id_unmop {X : Cᴹᵒᵖ} : (𝟙 (unmop X)).mop = 𝟙 X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mop_id_unmop {X : Cᴹᵒᵖ} : (𝟙 (unmop X)).mop = 𝟙 X := rfl

-- aesop prefers this lemma as a safe apply over Quiver.Hom.unmop_inj
/-
**CategoryTheory.MonoidalOpposite.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.MonoidalOpposite`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {x y : Cᴹᵒᵖ} {
f g : x ⟶ y}, f.unmop = g.unmop → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unmop_inj`：unmop_inj {X Y : Cᴹᵒᵖ} : Function.Injective (Quive
r.Hom.unmop : (X ⟶ Y) -> (unmop' X ⟶ unmop' Y))
-/
lemma MonoidalOpposite.hom_ext {x y : Cᴹᵒᵖ} {f g : x ⟶ y} (h : f.unmop = g.unmop) :
    f = g :=
  Quiver.Hom.unmop_inj h

variable (C)

/-- The identity functor on `C`, viewed as a functor from `C` to its monoidal opposite. -/
@[simps obj map] -- need to specify `obj, map` or else we generate `mopFunctor_obj_unmop`
/-
**CategoryTheory.mopFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：mopFunctor : C ⥤ Cᴹᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity functor on `C`, viewed as a functor from `C` to its monoidal opposi
te.
-/
def mopFunctor : C ⥤ Cᴹᵒᵖ := Functor.mk mop .mop
/-- The identity functor on `C`, viewed as a functor from the monoidal opposite of `C` to `C`. -/
@[simps obj map] -- not necessary but the symmetry with `mopFunctor` looks nicer
/-
**CategoryTheory.unmopFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：unmopFunctor : Cᴹᵒᵖ ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity functor on `C`, viewed as a functor from the monoidal opposite of `
C` to `C`.
-/
def unmopFunctor : Cᴹᵒᵖ ⥤ C := Functor.mk unmop .unmop

variable {C}

namespace Iso

/-- An isomorphism in `C` gives an isomorphism in `Cᴹᵒᵖ`. -/
/-
**CategoryTheory.Iso.mop** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：mop {X Y : C} (f : X ≅ Y) : mop X ≅ mop Y
参数：f : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism in `C` gives an isomorphism in `Cᴹᵒᵖ`.
-/
abbrev mop {X Y : C} (f : X ≅ Y) : mop X ≅ mop Y := (mopFunctor C).mapIso f

/-- An isomorphism in `Cᴹᵒᵖ` gives an isomorphism in `C`. -/
/-
**CategoryTheory.Iso.unmop** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：unmop {X Y : Cᴹᵒᵖ} (f : X ≅ Y) : unmop X ≅ unmop Y
参数：f : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism in `Cᴹᵒᵖ` gives an isomorphism in `C`.
-/
abbrev unmop {X Y : Cᴹᵒᵖ} (f : X ≅ Y) : unmop X ≅ unmop Y := (unmopFunctor C).mapIso f

end Iso

namespace IsIso

/-
**CategoryTheory.IsIso.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso f.mop :=
  (mopFunctor C).map_isIso f
/-
**CategoryTheory.IsIso.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) [IsIso f] : IsIso f.unmop :=
  (unmopFunctor C).map_isIso f

end IsIso

variable [MonoidalCategory.{v₁} C]

open Opposite MonoidalCategory CategoryTheory.Functor LaxMonoidal OplaxMonoidal

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.monoidalCategoryOp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：monoidalCategoryOp : MonoidalCategory Cᵒᵖ where tensorObj X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidalCategoryOp : MonoidalCategory Cᵒᵖ where
  tensorObj X Y := op (unop X ⊗ unop Y)
  whiskerLeft X _ _ f := (X.unop ◁ f.unop).op
  whiskerRight f X := (f.unop ▷ X.unop).op
  tensorHom f g := (f.unop ⊗ₘ g.unop).op
  tensorHom_def _ _ := Quiver.Hom.unop_inj (tensorHom_def' _ _)
  tensorHom_comp_tensorHom _ _ _ _ := Quiver.Hom.unop_inj <| by simp
  tensorUnit := op (𝟙_ C)
  associator X Y Z := (α_ (unop X) (unop Y) (unop Z)).symm.op
  leftUnitor X := (λ_ (unop X)).symm.op
  rightUnitor X := (ρ_ (unop X)).symm.op
  associator_naturality f g h := Quiver.Hom.unop_inj <| by simp
  leftUnitor_naturality f := Quiver.Hom.unop_inj <| by simp
  rightUnitor_naturality f := Quiver.Hom.unop_inj <| by simp
  triangle X Y := Quiver.Hom.unop_inj <| by dsimp; monoidal_coherence
  pentagon W X Y Z := Quiver.Hom.unop_inj <| by dsimp; monoidal_coherence

section OppositeLemmas

/-
**CategoryTheory.op_tensorObj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y : C),   Opposite.op (CategoryTheory.Monoidal
CategoryStruct.tensorObj X Y) =     CategoryTheory.MonoidalCategoryStruct.tensor
Obj (Opposite.op X) (Opposite.op Y)
参数：X Y : C；CategoryTheory.MonoidalCategoryStruct.tensorObj X Y；Opposite.op X；Opp
osite.op Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_tensorObj (X Y : C) : op (X ⊗ Y) = op X ⊗ op Y := rfl
/-
**CategoryTheory.unop_tensorObj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y : Cᵒᵖ),   Opposite.unop (CategoryTheory.Mono
idalCategoryStruct.tensorObj X Y) =     CategoryTheory.MonoidalCategoryStruct.te
nsorObj (Opposite.unop X) (Opposite.unop Y)
参数：X Y : Cᵒᵖ；CategoryTheory.MonoidalCategoryStruct.tensorObj X Y；Opposite.unop X
；Opposite.unop Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_tensorObj (X Y : Cᵒᵖ) : unop (X ⊗ Y) = unop X ⊗ unop Y := rfl
/-
**CategoryTheory.op_tensorUnit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C],   Opposite.op (CategoryTheory.MonoidalCategorySt
ruct.tensorUnit C) =     CategoryTheory.MonoidalCategoryStruct.tensorUnit Cᵒᵖ
参数：CategoryTheory.MonoidalCategoryStruct.tensorUnit C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_tensorUnit : op (𝟙_ C) = 𝟙_ Cᵒᵖ := rfl
/-
**CategoryTheory.unop_tensorUnit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C],   Opposite.unop (CategoryTheory.MonoidalCategory
Struct.tensorUnit Cᵒᵖ) =     CategoryTheory.MonoidalCategoryStruct.tensorUnit C
参数：CategoryTheory.MonoidalCategoryStruct.tensorUnit Cᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_tensorUnit : unop (𝟙_ Cᵒᵖ) = 𝟙_ C := rfl
/-
**CategoryTheory.op_tensorHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂), 
  (CategoryTheory.MonoidalCategoryStruct.tensorHom f g).op = CategoryTheory.Mono
idalCategoryStruct.tensorHom f.op g.op
参数：f : X₁ ⟶ Y₁；g : X₂ ⟶ Y₂；CategoryTheory.MonoidalCategoryStruct.tensorHom f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).op = f.op ⊗ₘ g.op := rfl
/-
**CategoryTheory.unop_tensorHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   {X₁ Y₁ X₂ Y₂ : Cᵒᵖ} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
,   (CategoryTheory.MonoidalCategoryStruct.tensorHom f g).unop =     CategoryThe
ory.MonoidalCategoryStruct.tensorHom f.unop g.unop
参数：f : X₁ ⟶ Y₁；g : X₂ ⟶ Y₂；CategoryTheory.MonoidalCategoryStruct.tensorHom f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_tensorHom {X₁ Y₁ X₂ Y₂ : Cᵒᵖ} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).unop = f.unop ⊗ₘ g.unop := rfl
/-
**CategoryTheory.op_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C)   {Y Z : C} (f : Y ⟶ Z),   (CategoryTheor
y.MonoidalCategoryStruct.whiskerLeft X f).op =     CategoryTheory.MonoidalCatego
ryStruct.whiskerLeft (Opposite.op X) f.op
参数：X : C；f : Y ⟶ Z；CategoryTheory.MonoidalCategoryStruct.whiskerLeft X f；Opposit
e.op X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) :
    (X ◁ f).op = op X ◁ f.op := rfl
/-
**CategoryTheory.unop_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᵒᵖ)   {Y Z : Cᵒᵖ} (f : Y ⟶ Z),   (CategoryT
heory.MonoidalCategoryStruct.whiskerLeft X f).unop =     CategoryTheory.Monoidal
CategoryStruct.whiskerLeft (Opposite.unop X) f.unop
参数：X : Cᵒᵖ；f : Y ⟶ Z；CategoryTheory.MonoidalCategoryStruct.whiskerLeft X f；Oppos
ite.unop X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_whiskerLeft (X : Cᵒᵖ) {Y Z : Cᵒᵖ} (f : Y ⟶ Z) :
    (X ◁ f).unop = unop X ◁ f.unop := rfl
/-
**CategoryTheory.op_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {X Y : C}   (f : X ⟶ Y) (Z : C),   (CategoryTheor
y.MonoidalCategoryStruct.whiskerRight f Z).op =     CategoryTheory.MonoidalCateg
oryStruct.whiskerRight f.op (Opposite.op Z)
参数：f : X ⟶ Y；Z : C；CategoryTheory.MonoidalCategoryStruct.whiskerRight f Z；Opposi
te.op Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    (f ▷ Z).op = f.op ▷ op Z := rfl
/-
**CategoryTheory.unop_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {X Y : Cᵒᵖ}   (f : X ⟶ Y) (Z : Cᵒᵖ),   (CategoryT
heory.MonoidalCategoryStruct.whiskerRight f Z).unop =     CategoryTheory.Monoida
lCategoryStruct.whiskerRight f.unop (Opposite.unop Z)
参数：f : X ⟶ Y；Z : Cᵒᵖ；CategoryTheory.MonoidalCategoryStruct.whiskerRight f Z；Oppo
site.unop Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_whiskerRight {X Y : Cᵒᵖ} (f : X ⟶ Y) (Z : Cᵒᵖ) :
    (f ▷ Z).unop = f.unop ▷ unop Z := rfl
/-
**CategoryTheory.op_associator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y Z : C),   (CategoryTheory.MonoidalCategorySt
ruct.associator X Y Z).op =     (CategoryTheory.MonoidalCategoryStruct.associato
r (Opposite.op X) (Opposite.op Y) (Opposite.op Z)).symm
参数：X Y Z : C；CategoryTheory.MonoidalCategoryStruct.associator X Y Z；CategoryTheo
ry.MonoidalCategoryStruct.associator (Opposite.op X) (Opposite.op Y) (Opposite.o
p Z)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_associator (X Y Z : C) :
    (α_ X Y Z).op = (α_ (op X) (op Y) (op Z)).symm := rfl
/-
**CategoryTheory.unop_associator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y Z : Cᵒᵖ),   (CategoryTheory.MonoidalCategory
Struct.associator X Y Z).unop =     (CategoryTheory.MonoidalCategoryStruct.assoc
iator (Opposite.unop X) (Opposite.unop Y) (Opposite.unop Z)).symm
参数：X Y Z : Cᵒᵖ；CategoryTheory.MonoidalCategoryStruct.associator X Y Z；CategoryTh
eory.MonoidalCategoryStruct.associator (Opposite.unop X) (Opposite.unop Y) (Oppo
site.unop Z)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_associator (X Y Z : Cᵒᵖ) :
    (α_ X Y Z).unop = (α_ (unop X) (unop Y) (unop Z)).symm := rfl
/-
**CategoryTheory.op_hom_associator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y Z : C),   (CategoryTheory.MonoidalCategorySt
ruct.associator X Y Z).hom.op =     (CategoryTheory.MonoidalCategoryStruct.assoc
iator (Opposite.op X) (Opposite.op Y) (Opposite.op Z)).inv
参数：X Y Z : C；CategoryTheory.MonoidalCategoryStruct.associator X Y Z；CategoryTheo
ry.MonoidalCategoryStruct.associator (Opposite.op X) (Opposite.op Y) (Opposite.o
p Z)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_hom_associator (X Y Z : C) :
    (α_ X Y Z).hom.op = (α_ (op X) (op Y) (op Z)).inv := rfl
/-
**CategoryTheory.unop_hom_associator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y Z : Cᵒᵖ),   (CategoryTheory.MonoidalCategory
Struct.associator X Y Z).hom.unop =     (CategoryTheory.MonoidalCategoryStruct.a
ssociator (Opposite.unop X) (Opposite.unop Y) (Opposite.unop Z)).inv
参数：X Y Z : Cᵒᵖ；CategoryTheory.MonoidalCategoryStruct.associator X Y Z；CategoryTh
eory.MonoidalCategoryStruct.associator (Opposite.unop X) (Opposite.unop Y) (Oppo
site.unop Z)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_hom_associator (X Y Z : Cᵒᵖ) :
    (α_ X Y Z).hom.unop = (α_ (unop X) (unop Y) (unop Z)).inv := rfl
/-
**CategoryTheory.op_inv_associator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y Z : C),   (CategoryTheory.MonoidalCategorySt
ruct.associator X Y Z).inv.op =     (CategoryTheory.MonoidalCategoryStruct.assoc
iator (Opposite.op X) (Opposite.op Y) (Opposite.op Z)).hom
参数：X Y Z : C；CategoryTheory.MonoidalCategoryStruct.associator X Y Z；CategoryTheo
ry.MonoidalCategoryStruct.associator (Opposite.op X) (Opposite.op Y) (Opposite.o
p Z)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_inv_associator (X Y Z : C) :
    (α_ X Y Z).inv.op = (α_ (op X) (op Y) (op Z)).hom := rfl
/-
**CategoryTheory.unop_inv_associator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y Z : Cᵒᵖ),   (CategoryTheory.MonoidalCategory
Struct.associator X Y Z).inv.unop =     (CategoryTheory.MonoidalCategoryStruct.a
ssociator (Opposite.unop X) (Opposite.unop Y) (Opposite.unop Z)).hom
参数：X Y Z : Cᵒᵖ；CategoryTheory.MonoidalCategoryStruct.associator X Y Z；CategoryTh
eory.MonoidalCategoryStruct.associator (Opposite.unop X) (Opposite.unop Y) (Oppo
site.unop Z)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_inv_associator (X Y Z : Cᵒᵖ) :
    (α_ X Y Z).inv.unop = (α_ (unop X) (unop Y) (unop Z)).hom := rfl
/-
**CategoryTheory.op_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C),   (CategoryTheory.MonoidalCategoryStruct
.leftUnitor X).op =     (CategoryTheory.MonoidalCategoryStruct.leftUnitor (Oppos
ite.op X)).symm
参数：X : C；CategoryTheory.MonoidalCategoryStruct.leftUnitor X；CategoryTheory.Monoi
dalCategoryStruct.leftUnitor (Opposite.op X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_leftUnitor (X : C) : (λ_ X).op = (λ_ (op X)).symm := rfl
/-
**CategoryTheory.unop_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᵒᵖ),   (CategoryTheory.MonoidalCategoryStru
ct.leftUnitor X).unop =     (CategoryTheory.MonoidalCategoryStruct.leftUnitor (O
pposite.unop X)).symm
参数：X : Cᵒᵖ；CategoryTheory.MonoidalCategoryStruct.leftUnitor X；CategoryTheory.Mon
oidalCategoryStruct.leftUnitor (Opposite.unop X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_leftUnitor (X : Cᵒᵖ) : (λ_ X).unop = (λ_ (unop X)).symm := rfl
/-
**CategoryTheory.op_hom_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C),   (CategoryTheory.MonoidalCategoryStruct
.leftUnitor X).hom.op =     (CategoryTheory.MonoidalCategoryStruct.leftUnitor (O
pposite.op X)).inv
参数：X : C；CategoryTheory.MonoidalCategoryStruct.leftUnitor X；CategoryTheory.Monoi
dalCategoryStruct.leftUnitor (Opposite.op X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_hom_leftUnitor (X : C) : (λ_ X).hom.op = (λ_ (op X)).inv := rfl
/-
**CategoryTheory.unop_hom_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᵒᵖ),   (CategoryTheory.MonoidalCategoryStru
ct.leftUnitor X).hom.unop =     (CategoryTheory.MonoidalCategoryStruct.leftUnito
r (Opposite.unop X)).inv
参数：X : Cᵒᵖ；CategoryTheory.MonoidalCategoryStruct.leftUnitor X；CategoryTheory.Mon
oidalCategoryStruct.leftUnitor (Opposite.unop X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_hom_leftUnitor (X : Cᵒᵖ) : (λ_ X).hom.unop = (λ_ (unop X)).inv := rfl
/-
**CategoryTheory.op_inv_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C),   (CategoryTheory.MonoidalCategoryStruct
.leftUnitor X).inv.op =     (CategoryTheory.MonoidalCategoryStruct.leftUnitor (O
pposite.op X)).hom
参数：X : C；CategoryTheory.MonoidalCategoryStruct.leftUnitor X；CategoryTheory.Monoi
dalCategoryStruct.leftUnitor (Opposite.op X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_inv_leftUnitor (X : C) : (λ_ X).inv.op = (λ_ (op X)).hom := rfl
/-
**CategoryTheory.unop_inv_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᵒᵖ),   (CategoryTheory.MonoidalCategoryStru
ct.leftUnitor X).inv.unop =     (CategoryTheory.MonoidalCategoryStruct.leftUnito
r (Opposite.unop X)).hom
参数：X : Cᵒᵖ；CategoryTheory.MonoidalCategoryStruct.leftUnitor X；CategoryTheory.Mon
oidalCategoryStruct.leftUnitor (Opposite.unop X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_inv_leftUnitor (X : Cᵒᵖ) : (λ_ X).inv.unop = (λ_ (unop X)).hom := rfl
/-
**CategoryTheory.op_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C),   (CategoryTheory.MonoidalCategoryStruct
.rightUnitor X).op =     (CategoryTheory.MonoidalCategoryStruct.rightUnitor (Opp
osite.op X)).symm
参数：X : C；CategoryTheory.MonoidalCategoryStruct.rightUnitor X；CategoryTheory.Mono
idalCategoryStruct.rightUnitor (Opposite.op X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_rightUnitor (X : C) : (ρ_ X).op = (ρ_ (op X)).symm := rfl
/-
**CategoryTheory.unop_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᵒᵖ),   (CategoryTheory.MonoidalCategoryStru
ct.rightUnitor X).unop =     (CategoryTheory.MonoidalCategoryStruct.rightUnitor 
(Opposite.unop X)).symm
参数：X : Cᵒᵖ；CategoryTheory.MonoidalCategoryStruct.rightUnitor X；CategoryTheory.Mo
noidalCategoryStruct.rightUnitor (Opposite.unop X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_rightUnitor (X : Cᵒᵖ) : (ρ_ X).unop = (ρ_ (unop X)).symm := rfl
/-
**CategoryTheory.op_hom_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C),   (CategoryTheory.MonoidalCategoryStruct
.rightUnitor X).hom.op =     (CategoryTheory.MonoidalCategoryStruct.rightUnitor 
(Opposite.op X)).inv
参数：X : C；CategoryTheory.MonoidalCategoryStruct.rightUnitor X；CategoryTheory.Mono
idalCategoryStruct.rightUnitor (Opposite.op X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_hom_rightUnitor (X : C) : (ρ_ X).hom.op = (ρ_ (op X)).inv := rfl
/-
**CategoryTheory.unop_hom_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᵒᵖ),   (CategoryTheory.MonoidalCategoryStru
ct.rightUnitor X).hom.unop =     (CategoryTheory.MonoidalCategoryStruct.rightUni
tor (Opposite.unop X)).inv
参数：X : Cᵒᵖ；CategoryTheory.MonoidalCategoryStruct.rightUnitor X；CategoryTheory.Mo
noidalCategoryStruct.rightUnitor (Opposite.unop X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_hom_rightUnitor (X : Cᵒᵖ) : (ρ_ X).hom.unop = (ρ_ (unop X)).inv := rfl
/-
**CategoryTheory.op_inv_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C),   (CategoryTheory.MonoidalCategoryStruct
.rightUnitor X).inv.op =     (CategoryTheory.MonoidalCategoryStruct.rightUnitor 
(Opposite.op X)).hom
参数：X : C；CategoryTheory.MonoidalCategoryStruct.rightUnitor X；CategoryTheory.Mono
idalCategoryStruct.rightUnitor (Opposite.op X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_inv_rightUnitor (X : C) : (ρ_ X).inv.op = (ρ_ (op X)).hom := rfl
/-
**CategoryTheory.unop_inv_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᵒᵖ),   (CategoryTheory.MonoidalCategoryStru
ct.rightUnitor X).inv.unop =     (CategoryTheory.MonoidalCategoryStruct.rightUni
tor (Opposite.unop X)).hom
参数：X : Cᵒᵖ；CategoryTheory.MonoidalCategoryStruct.rightUnitor X；CategoryTheory.Mo
noidalCategoryStruct.rightUnitor (Opposite.unop X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_inv_rightUnitor (X : Cᵒᵖ) : (ρ_ X).inv.unop = (ρ_ (unop X)).hom := rfl

end OppositeLemmas

/-
**CategoryTheory.op_tensor_op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：op_tensor_op {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f.op otimesₘ g.op = (
f otimesₘ g).op
参数：f : W ⟶ X；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_tensor_op {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f.op ⊗ₘ g.op = (f ⊗ₘ g).op := rfl
/-
**CategoryTheory.unop_tensor_unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unop_tensor_unop {W X Y Z : Cᵒᵖ} (f : W ⟶ X) (g : Y ⟶ Z) : f.unop otimesₘ 
g.unop = (f otimesₘ g).unop
参数：f : W ⟶ X；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_tensor_unop {W X Y Z : Cᵒᵖ} (f : W ⟶ X) (g : Y ⟶ Z) :
    f.unop ⊗ₘ g.unop = (f ⊗ₘ g).unop := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.monoidalCategoryMop** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：monoidalCategoryMop : MonoidalCategory Cᴹᵒᵖ where tensorObj X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidalCategoryMop : MonoidalCategory Cᴹᵒᵖ where
  tensorObj X Y := mop (unmop Y ⊗ unmop X)
  whiskerLeft X _ _ f := (f.unmop ▷ X.unmop).mop
  whiskerRight f X := (X.unmop ◁ f.unmop).mop
  tensorHom f g := (g.unmop ⊗ₘ f.unmop).mop
  tensorHom_def _ _ := Quiver.Hom.unmop_inj (tensorHom_def' _ _)
  tensorHom_comp_tensorHom _ _ _ _ := Quiver.Hom.unmop_inj <| by simp
  tensorUnit := mop (𝟙_ C)
  associator X Y Z := (α_ (unmop Z) (unmop Y) (unmop X)).symm.mop
  leftUnitor X := (ρ_ (unmop X)).mop
  rightUnitor X := (λ_ (unmop X)).mop
  associator_naturality f g h := Quiver.Hom.unmop_inj <| by simp
  leftUnitor_naturality f := Quiver.Hom.unmop_inj <| by simp
  rightUnitor_naturality f := Quiver.Hom.unmop_inj <| by simp
  triangle X Y := Quiver.Hom.unmop_inj <| by dsimp; monoidal_coherence
  pentagon W X Y Z := Quiver.Hom.unmop_inj <| by dsimp; monoidal_coherence

-- it would be nice if we could autogenerate all of these somehow
section MonoidalOppositeLemmas

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_tensorObj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y : C),   { unmop := CategoryTheory.MonoidalCa
tegoryStruct.tensorObj X Y } =     CategoryTheory.MonoidalCategoryStruct.tensorO
bj { unmop := Y } { unmop := X }
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_tensorObj (X Y : C) : mop (X ⊗ Y) = mop Y ⊗ mop X := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_tensorObj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y : Cᴹᵒᵖ),   (CategoryTheory.MonoidalCategoryS
truct.tensorObj X Y).unmop =     CategoryTheory.MonoidalCategoryStruct.tensorObj
 Y.unmop X.unmop
参数：X Y : Cᴹᵒᵖ；CategoryTheory.MonoidalCategoryStruct.tensorObj X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_tensorObj (X Y : Cᴹᵒᵖ) : unmop (X ⊗ Y) = unmop Y ⊗ unmop X := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_tensorUnit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C],   { unmop := CategoryTheory.MonoidalCategoryStru
ct.tensorUnit C } =     CategoryTheory.MonoidalCategoryStruct.tensorUnit Cᴹᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_tensorUnit : mop (𝟙_ C) = 𝟙_ Cᴹᵒᵖ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_tensorUnit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C],   (CategoryTheory.MonoidalCategoryStruct.tensorU
nit Cᴹᵒᵖ).unmop = CategoryTheory.MonoidalCategoryStruct.tensorUnit C
参数：CategoryTheory.MonoidalCategoryStruct.tensorUnit Cᴹᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_tensorUnit : unmop (𝟙_ Cᴹᵒᵖ) = 𝟙_ C := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_tensorHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂), 
  (CategoryTheory.MonoidalCategoryStruct.tensorHom f g).mop =     CategoryTheory
.MonoidalCategoryStruct.tensorHom g.mop f.mop
参数：f : X₁ ⟶ Y₁；g : X₂ ⟶ Y₂；CategoryTheory.MonoidalCategoryStruct.tensorHom f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).mop = g.mop ⊗ₘ f.mop := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_tensorHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   {X₁ Y₁ X₂ Y₂ : Cᴹᵒᵖ} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂
),   (CategoryTheory.MonoidalCategoryStruct.tensorHom f g).unmop =     CategoryT
heory.MonoidalCategoryStruct.tensorHom g.unmop f.unmop
参数：f : X₁ ⟶ Y₁；g : X₂ ⟶ Y₂；CategoryTheory.MonoidalCategoryStruct.tensorHom f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_tensorHom {X₁ Y₁ X₂ Y₂ : Cᴹᵒᵖ} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).unmop = g.unmop ⊗ₘ f.unmop := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C)   {Y Z : C} (f : Y ⟶ Z),   (CategoryTheor
y.MonoidalCategoryStruct.whiskerLeft X f).mop =     CategoryTheory.MonoidalCateg
oryStruct.whiskerRight f.mop { unmop := X }
参数：X : C；f : Y ⟶ Z；CategoryTheory.MonoidalCategoryStruct.whiskerLeft X f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) :
    (X ◁ f).mop = f.mop ▷ mop X := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᴹᵒᵖ)   {Y Z : Cᴹᵒᵖ} (f : Y ⟶ Z),   (Categor
yTheory.MonoidalCategoryStruct.whiskerLeft X f).unmop =     CategoryTheory.Monoi
dalCategoryStruct.whiskerRight f.unmop X.unmop
参数：X : Cᴹᵒᵖ；f : Y ⟶ Z；CategoryTheory.MonoidalCategoryStruct.whiskerLeft X f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_whiskerLeft (X : Cᴹᵒᵖ) {Y Z : Cᴹᵒᵖ} (f : Y ⟶ Z) :
    (X ◁ f).unmop = f.unmop ▷ unmop X := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {X Y : C}   (f : X ⟶ Y) (Z : C),   (CategoryTheor
y.MonoidalCategoryStruct.whiskerRight f Z).mop =     CategoryTheory.MonoidalCate
goryStruct.whiskerLeft { unmop := Z } f.mop
参数：f : X ⟶ Y；Z : C；CategoryTheory.MonoidalCategoryStruct.whiskerRight f Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    (f ▷ Z).mop = mop Z ◁ f.mop := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {X Y : Cᴹᵒᵖ}   (f : X ⟶ Y) (Z : Cᴹᵒᵖ),   (Categor
yTheory.MonoidalCategoryStruct.whiskerRight f Z).unmop =     CategoryTheory.Mono
idalCategoryStruct.whiskerLeft Z.unmop f.unmop
参数：f : X ⟶ Y；Z : Cᴹᵒᵖ；CategoryTheory.MonoidalCategoryStruct.whiskerRight f Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_whiskerRight {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) (Z : Cᴹᵒᵖ) :
    (f ▷ Z).unmop = unmop Z ◁ f.unmop := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_associator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y Z : C),   (CategoryTheory.MonoidalCategorySt
ruct.associator X Y Z).mop =     (CategoryTheory.MonoidalCategoryStruct.associat
or { unmop := Z } { unmop := Y } { unmop := X }).symm
参数：X Y Z : C；CategoryTheory.MonoidalCategoryStruct.associator X Y Z；CategoryTheo
ry.MonoidalCategoryStruct.associator { unmop := Z } { unmop := Y } { unmop := X 
}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_associator (X Y Z : C) :
    (α_ X Y Z).mop = (α_ (mop Z) (mop Y) (mop X)).symm := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_associator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y Z : Cᴹᵒᵖ),   (CategoryTheory.MonoidalCategor
yStruct.associator X Y Z).unmop =     (CategoryTheory.MonoidalCategoryStruct.ass
ociator Z.unmop Y.unmop X.unmop).symm
参数：X Y Z : Cᴹᵒᵖ；CategoryTheory.MonoidalCategoryStruct.associator X Y Z；CategoryT
heory.MonoidalCategoryStruct.associator Z.unmop Y.unmop X.unmop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_associator (X Y Z : Cᴹᵒᵖ) :
    (α_ X Y Z).unmop = (α_ (unmop Z) (unmop Y) (unmop X)).symm := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_hom_associator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y Z : C),   (CategoryTheory.MonoidalCategorySt
ruct.associator X Y Z).hom.mop =     (CategoryTheory.MonoidalCategoryStruct.asso
ciator { unmop := Z } { unmop := Y } { unmop := X }).inv
参数：X Y Z : C；CategoryTheory.MonoidalCategoryStruct.associator X Y Z；CategoryTheo
ry.MonoidalCategoryStruct.associator { unmop := Z } { unmop := Y } { unmop := X 
}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_hom_associator (X Y Z : C) :
    (α_ X Y Z).hom.mop = (α_ (mop Z) (mop Y) (mop X)).inv := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_hom_associator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y Z : Cᴹᵒᵖ),   (CategoryTheory.MonoidalCategor
yStruct.associator X Y Z).hom.unmop =     (CategoryTheory.MonoidalCategoryStruct
.associator Z.unmop Y.unmop X.unmop).inv
参数：X Y Z : Cᴹᵒᵖ；CategoryTheory.MonoidalCategoryStruct.associator X Y Z；CategoryT
heory.MonoidalCategoryStruct.associator Z.unmop Y.unmop X.unmop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_hom_associator (X Y Z : Cᴹᵒᵖ) :
    (α_ X Y Z).hom.unmop = (α_ (unmop Z) (unmop Y) (unmop X)).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_inv_associator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y Z : C),   (CategoryTheory.MonoidalCategorySt
ruct.associator X Y Z).inv.mop =     (CategoryTheory.MonoidalCategoryStruct.asso
ciator { unmop := Z } { unmop := Y } { unmop := X }).hom
参数：X Y Z : C；CategoryTheory.MonoidalCategoryStruct.associator X Y Z；CategoryTheo
ry.MonoidalCategoryStruct.associator { unmop := Z } { unmop := Y } { unmop := X 
}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_inv_associator (X Y Z : C) :
    (α_ X Y Z).inv.mop = (α_ (mop Z) (mop Y) (mop X)).hom := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_inv_associator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X Y Z : Cᴹᵒᵖ),   (CategoryTheory.MonoidalCategor
yStruct.associator X Y Z).inv.unmop =     (CategoryTheory.MonoidalCategoryStruct
.associator Z.unmop Y.unmop X.unmop).hom
参数：X Y Z : Cᴹᵒᵖ；CategoryTheory.MonoidalCategoryStruct.associator X Y Z；CategoryT
heory.MonoidalCategoryStruct.associator Z.unmop Y.unmop X.unmop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_inv_associator (X Y Z : Cᴹᵒᵖ) :
    (α_ X Y Z).inv.unmop = (α_ (unmop Z) (unmop Y) (unmop X)).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C),   (CategoryTheory.MonoidalCategoryStruct
.leftUnitor X).mop =     CategoryTheory.MonoidalCategoryStruct.rightUnitor { unm
op := X }
参数：X : C；CategoryTheory.MonoidalCategoryStruct.leftUnitor X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_leftUnitor (X : C) : (λ_ X).mop = (ρ_ (mop X)) := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᴹᵒᵖ),   (CategoryTheory.MonoidalCategoryStr
uct.leftUnitor X).unmop = CategoryTheory.MonoidalCategoryStruct.rightUnitor X.un
mop
参数：X : Cᴹᵒᵖ；CategoryTheory.MonoidalCategoryStruct.leftUnitor X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_leftUnitor (X : Cᴹᵒᵖ) : (λ_ X).unmop = ρ_ (unmop X) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_hom_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C),   (CategoryTheory.MonoidalCategoryStruct
.leftUnitor X).hom.mop =     (CategoryTheory.MonoidalCategoryStruct.rightUnitor 
{ unmop := X }).hom
参数：X : C；CategoryTheory.MonoidalCategoryStruct.leftUnitor X；CategoryTheory.Monoi
dalCategoryStruct.rightUnitor { unmop := X }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_hom_leftUnitor (X : C) : (λ_ X).hom.mop = (ρ_ (mop X)).hom := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_hom_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᴹᵒᵖ),   (CategoryTheory.MonoidalCategoryStr
uct.leftUnitor X).hom.unmop =     (CategoryTheory.MonoidalCategoryStruct.rightUn
itor X.unmop).hom
参数：X : Cᴹᵒᵖ；CategoryTheory.MonoidalCategoryStruct.leftUnitor X；CategoryTheory.Mo
noidalCategoryStruct.rightUnitor X.unmop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_hom_leftUnitor (X : Cᴹᵒᵖ) : (λ_ X).hom.unmop = (ρ_ (unmop X)).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_inv_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C),   (CategoryTheory.MonoidalCategoryStruct
.leftUnitor X).inv.mop =     (CategoryTheory.MonoidalCategoryStruct.rightUnitor 
{ unmop := X }).inv
参数：X : C；CategoryTheory.MonoidalCategoryStruct.leftUnitor X；CategoryTheory.Monoi
dalCategoryStruct.rightUnitor { unmop := X }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_inv_leftUnitor (X : C) : (λ_ X).inv.mop = (ρ_ (mop X)).inv := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_inv_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᴹᵒᵖ),   (CategoryTheory.MonoidalCategoryStr
uct.leftUnitor X).inv.unmop =     (CategoryTheory.MonoidalCategoryStruct.rightUn
itor X.unmop).inv
参数：X : Cᴹᵒᵖ；CategoryTheory.MonoidalCategoryStruct.leftUnitor X；CategoryTheory.Mo
noidalCategoryStruct.rightUnitor X.unmop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_inv_leftUnitor (X : Cᴹᵒᵖ) : (λ_ X).inv.unmop = (ρ_ (unmop X)).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C),   (CategoryTheory.MonoidalCategoryStruct
.rightUnitor X).mop =     CategoryTheory.MonoidalCategoryStruct.leftUnitor { unm
op := X }
参数：X : C；CategoryTheory.MonoidalCategoryStruct.rightUnitor X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_rightUnitor (X : C) : (ρ_ X).mop = (λ_ (mop X)) := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᴹᵒᵖ),   (CategoryTheory.MonoidalCategoryStr
uct.rightUnitor X).unmop = CategoryTheory.MonoidalCategoryStruct.leftUnitor X.un
mop
参数：X : Cᴹᵒᵖ；CategoryTheory.MonoidalCategoryStruct.rightUnitor X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_rightUnitor (X : Cᴹᵒᵖ) : (ρ_ X).unmop = λ_ (unmop X) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_hom_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C),   (CategoryTheory.MonoidalCategoryStruct
.rightUnitor X).hom.mop =     (CategoryTheory.MonoidalCategoryStruct.leftUnitor 
{ unmop := X }).hom
参数：X : C；CategoryTheory.MonoidalCategoryStruct.rightUnitor X；CategoryTheory.Mono
idalCategoryStruct.leftUnitor { unmop := X }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_hom_rightUnitor (X : C) : (ρ_ X).hom.mop = (λ_ (mop X)).hom := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_hom_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᴹᵒᵖ),   (CategoryTheory.MonoidalCategoryStr
uct.rightUnitor X).hom.unmop =     (CategoryTheory.MonoidalCategoryStruct.leftUn
itor X.unmop).hom
参数：X : Cᴹᵒᵖ；CategoryTheory.MonoidalCategoryStruct.rightUnitor X；CategoryTheory.M
onoidalCategoryStruct.leftUnitor X.unmop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_hom_rightUnitor (X : Cᴹᵒᵖ) : (ρ_ X).hom.unmop = (λ_ (unmop X)).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.mop_inv_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : C),   (CategoryTheory.MonoidalCategoryStruct
.rightUnitor X).inv.mop =     (CategoryTheory.MonoidalCategoryStruct.leftUnitor 
{ unmop := X }).inv
参数：X : C；CategoryTheory.MonoidalCategoryStruct.rightUnitor X；CategoryTheory.Mono
idalCategoryStruct.leftUnitor { unmop := X }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_inv_rightUnitor (X : C) : (ρ_ X).inv.mop = (λ_ (mop X)).inv := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.unmop_inv_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (X : Cᴹᵒᵖ),   (CategoryTheory.MonoidalCategoryStr
uct.rightUnitor X).inv.unmop =     (CategoryTheory.MonoidalCategoryStruct.leftUn
itor X.unmop).inv
参数：X : Cᴹᵒᵖ；CategoryTheory.MonoidalCategoryStruct.rightUnitor X；CategoryTheory.M
onoidalCategoryStruct.leftUnitor X.unmop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_inv_rightUnitor (X : Cᴹᵒᵖ) : (ρ_ X).inv.unmop = (λ_ (unmop X)).inv := rfl

end MonoidalOppositeLemmas

variable (C)

set_option backward.defeqAttrib.useBackward true in
set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The (identity) equivalence between `C` and its monoidal opposite. -/
/-
**CategoryTheory.MonoidalOpposite.mopEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MonoidalOpposite`。
形式化陈述：(C : Type u₁) → [inst : CategoryTheory.Category.{v₁, u₁} C] → C ≌ Cᴹᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (identity) equivalence between `C` and its monoidal opposite.
-/
@[simps] def MonoidalOpposite.mopEquiv : C ≌ Cᴹᵒᵖ where
  functor   := mopFunctor C
  inverse   := unmopFunctor C
  unitIso   := Iso.refl _
  counitIso := Iso.refl _

/-- The (identity) equivalence between `Cᴹᵒᵖ` and `C`. -/
/-
**CategoryTheory.MonoidalOpposite.unmopEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.MonoidalOpposite`。
形式化陈述：(C : Type u₁) → [inst : CategoryTheory.Category.{v₁, u₁} C] → Cᴹᵒᵖ ≌ C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (identity) equivalence between `Cᴹᵒᵖ` and `C`.
-/
@[simps!] def MonoidalOpposite.unmopEquiv : Cᴹᵒᵖ ≌ C := (mopEquiv C).symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence between `C` and its monoidal opposite's monoidal opposite. -/
/-
**CategoryTheory.MonoidalOpposite.mopMopEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MonoidalOpposite`。
形式化陈述：(C : Type u₁) → [inst : CategoryTheory.Category.{v₁, u₁} C] → Cᴹᵒᵖᴹᵒᵖ ≌ C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `C` and its monoidal opposite's monoidal opposite.
-/
@[simps!] def MonoidalOpposite.mopMopEquivalence : Cᴹᵒᵖᴹᵒᵖ ≌ C :=
  .trans (MonoidalOpposite.unmopEquiv Cᴹᵒᵖ) (MonoidalOpposite.unmopEquiv C)

set_option backward.isDefEq.respectTransparency.types false in
@[simps!]
/-
**CategoryTheory.MonoidalOpposite.mopMopEquivalenceFunctorMonoidal** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.MonoidalOpposite`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       (CategoryTheory.MonoidalOpposite.
mopMopEquivalence C).functor.Monoidal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.MonoidalOpposite.mopMopEquivalenceInverseMonoidal** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.MonoidalOpposite`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       (CategoryTheory.MonoidalOpposite.
mopMopEquivalence C).inverse.Monoidal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (mopMopEquivalence C).IsMonoidal where
  leftAdjoint_ε := by
    simp [ε, η, mopMopEquivalence, Equivalence.trans, unmopEquiv, ε]
  leftAdjoint_μ X Y := by
    simp [μ, δ, mopMopEquivalence, Equivalence.trans, unmopEquiv, μ]

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `mop X ⊗ mop Y = mop (Y ⊗ X)` as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.MonoidalOpposite.tensorIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.MonoidalOpposite`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       CategoryTheory.MonoidalCategory.t
ensor Cᴹᵒᵖ ≅         ((CategoryTheory.unmopFunctor C).prod (CategoryTheory.unmop
Functor C)).comp           ((CategoryTheory.Prod.swap C C).comp             ((Ca
tegoryTheory.MonoidalCategory.tensor C).comp (CategoryTheory.mopFunctor C)))
参数：CategoryTheory.unmopFunctor C；CategoryTheory.unmopFunctor C；CategoryTheory.Pr
od.swap C C；(CategoryTheory.MonoidalCategory.tensor C).comp (CategoryTheory.mopF
unctor C)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identification `mop X ⊗ mop Y = mop (Y ⊗ X)` as a natural isomorphism.
-/
def MonoidalOpposite.tensorIso :
    tensor Cᴹᵒᵖ ≅ (unmopFunctor C).prod (unmopFunctor C) ⋙
      Prod.swap C C ⋙ tensor C ⋙ mopFunctor C :=
  Iso.refl _

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `X ⊗ - = mop (- ⊗ unmop X)` as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.MonoidalOpposite.tensorLeftIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.MonoidalOpposite`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       (X : Cᴹᵒᵖ) →         CategoryTheo
ry.MonoidalCategory.tensorLeft X ≅           (CategoryTheory.unmopFunctor C).com
p             ((CategoryTheory.MonoidalCategory.tensorRight X.unmop).comp (Categ
oryTheory.mopFunctor C))
参数：X : Cᴹᵒᵖ；CategoryTheory.unmopFunctor C；(CategoryTheory.MonoidalCategory.tenso
rRight X.unmop).comp (CategoryTheory.mopFunctor C)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identification `X ⊗ - = mop (- ⊗ unmop X)` as a natural isomorphism.
-/
def MonoidalOpposite.tensorLeftIso (X : Cᴹᵒᵖ) :
    tensorLeft X ≅ unmopFunctor C ⋙ tensorRight (unmop X) ⋙ mopFunctor C :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `mop X ⊗ - = mop (- ⊗ X)` as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.MonoidalOpposite.tensorLeftMopIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MonoidalOpposite`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       (X : C) →         CategoryTheory.
MonoidalCategory.tensorLeft { unmop := X } ≅           (CategoryTheory.unmopFunc
tor C).comp             ((CategoryTheory.MonoidalCategory.tensorRight X).comp (C
ategoryTheory.mopFunctor C))
参数：X : C；CategoryTheory.unmopFunctor C；(CategoryTheory.MonoidalCategory.tensorRi
ght X).comp (CategoryTheory.mopFunctor C)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identification `mop X ⊗ - = mop (- ⊗ X)` as a natural isomorphism.
-/
def MonoidalOpposite.tensorLeftMopIso (X : C) :
    tensorLeft (mop X) ≅ unmopFunctor C ⋙ tensorRight X ⋙ mopFunctor C :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `unmop X ⊗ - = unmop (mop - ⊗ X)` as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.MonoidalOpposite.tensorLeftUnmopIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MonoidalOpposite`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       (X : Cᴹᵒᵖ) →         CategoryTheo
ry.MonoidalCategory.tensorLeft X.unmop ≅           (CategoryTheory.mopFunctor C)
.comp             ((CategoryTheory.MonoidalCategory.tensorRight X).comp (Categor
yTheory.unmopFunctor C))
参数：X : Cᴹᵒᵖ；CategoryTheory.mopFunctor C；(CategoryTheory.MonoidalCategory.tensorR
ight X).comp (CategoryTheory.unmopFunctor C)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identification `unmop X ⊗ - = unmop (mop - ⊗ X)` as a natural isomorphism.
-/
def MonoidalOpposite.tensorLeftUnmopIso (X : Cᴹᵒᵖ) :
    tensorLeft (unmop X) ≅ mopFunctor C ⋙ tensorRight X ⋙ unmopFunctor C :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `- ⊗ X = mop (unmop X ⊗ -)` as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.MonoidalOpposite.tensorRightIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.MonoidalOpposite`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       (X : Cᴹᵒᵖ) →         CategoryTheo
ry.MonoidalCategory.tensorRight X ≅           (CategoryTheory.unmopFunctor C).co
mp             ((CategoryTheory.MonoidalCategory.tensorLeft X.unmop).comp (Categ
oryTheory.mopFunctor C))
参数：X : Cᴹᵒᵖ；CategoryTheory.unmopFunctor C；(CategoryTheory.MonoidalCategory.tenso
rLeft X.unmop).comp (CategoryTheory.mopFunctor C)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identification `- ⊗ X = mop (unmop X ⊗ -)` as a natural isomorphism.
-/
def MonoidalOpposite.tensorRightIso (X : Cᴹᵒᵖ) :
    tensorRight X ≅ unmopFunctor C ⋙ tensorLeft (unmop X) ⋙ mopFunctor C :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `- ⊗ mop X = mop (- ⊗ unmop X)` as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.MonoidalOpposite.tensorRightMopIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MonoidalOpposite`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       (X : C) →         CategoryTheory.
MonoidalCategory.tensorRight { unmop := X } ≅           (CategoryTheory.unmopFun
ctor C).comp             ((CategoryTheory.MonoidalCategory.tensorLeft X).comp (C
ategoryTheory.mopFunctor C))
参数：X : C；CategoryTheory.unmopFunctor C；(CategoryTheory.MonoidalCategory.tensorLe
ft X).comp (CategoryTheory.mopFunctor C)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identification `- ⊗ mop X = mop (- ⊗ unmop X)` as a natural isomorphism.
-/
def MonoidalOpposite.tensorRightMopIso (X : C) :
    tensorRight (mop X) ≅ unmopFunctor C ⋙ tensorLeft X ⋙ mopFunctor C :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification `- ⊗ unmop X = unmop (X ⊗ mop -)` as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.MonoidalOpposite.tensorRightUnmopIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.MonoidalOpposite`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       (X : Cᴹᵒᵖ) →         CategoryTheo
ry.MonoidalCategory.tensorRight X.unmop ≅           (CategoryTheory.mopFunctor C
).comp             ((CategoryTheory.MonoidalCategory.tensorLeft X).comp (Categor
yTheory.unmopFunctor C))
参数：X : Cᴹᵒᵖ；CategoryTheory.mopFunctor C；(CategoryTheory.MonoidalCategory.tensorL
eft X).comp (CategoryTheory.unmopFunctor C)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identification `- ⊗ unmop X = unmop (X ⊗ mop -)` as a natural isomorphism.
-/
def MonoidalOpposite.tensorRightUnmopIso (X : Cᴹᵒᵖ) :
    tensorRight (unmop X) ≅ mopFunctor C ⋙ tensorLeft X ⋙ unmopFunctor C :=
  Iso.refl _

@[simps]
/-
**CategoryTheory.monoidalOpOp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：monoidalOpOp : (opOp C).Monoidal where ε
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.monoidalUnopUnop** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：monoidalUnopUnop : (unopUnop C).Monoidal where ε
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (opOpEquivalence C).functor.Monoidal := monoidalUnopUnop
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (opOpEquivalence C).inverse.Monoidal := monoidalOpOp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (opOpEquivalence C).IsMonoidal where
  leftAdjoint_ε := by simp [opOpEquivalence]
  leftAdjoint_μ := by simp [opOpEquivalence]

end CategoryTheory

