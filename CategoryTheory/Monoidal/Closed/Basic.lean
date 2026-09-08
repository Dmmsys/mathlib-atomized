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
/-- An object `X` is (right) closed if `(X ⊗ -)` is a left adjoint. -/
/-
**CategoryTheory.Closed** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.MonoidalCategory C] → C → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` is (right) closed if `(X ⊗ -)` is a left adjoint.
-/
class Closed {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (X : C) where
  /-- a choice of a right adjoint for `tensorLeft X` -/
  rightAdj : C ⥤ C
  /-- `tensorLeft X` is a left adjoint -/
  adj : tensorLeft X ⊣ rightAdj

/-- A monoidal category `C` is (right) monoidal closed if every object is (right) closed. -/
/-
**CategoryTheory.MonoidalClosed** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：MonoidalClosed (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] wher
e closed (X : C) : Closed X
参数：C : Type u；X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoidal category `C` is (right) monoidal closed if every object is (right) cl
osed.
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
/-
**CategoryTheory.tensorClosed** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：tensorClosed {X Y : C} (hX : Closed X) (hY : Closed Y) : Closed (X otimes 
Y) where rightAdj
参数：hX : Closed X；hY : Closed Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` and `Y` are closed then `X ⊗ Y` is.
This isn't an instance because it's not usually how we want to construct interna
l homs,
we'll usually prove all objects are closed uniformly.
-/
def tensorClosed {X Y : C} (hX : Closed X) (hY : Closed Y) : Closed (X ⊗ Y) where
  rightAdj := Closed.rightAdj X ⋙ Closed.rightAdj Y
  adj := (hY.adj.comp hX.adj).ofNatIsoLeft (MonoidalCategory.tensorLeftTensor X Y).symm

/-- The unit object is always closed.
This isn't an instance because most of the time we'll prove closedness for all objects at once,
rather than just for this one.
-/
@[instance_reducible]
/-
**CategoryTheory.unitClosed** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：unitClosed : Closed (𝟙_ C) where rightAdj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit object is always closed.
This isn't an instance because most of the time we'll prove closedness for all o
bjects at once,
rather than just for this one.
-/
def unitClosed : Closed (𝟙_ C) where
  rightAdj := 𝟭 C
  adj := Adjunction.id.ofNatIsoLeft (MonoidalCategory.leftUnitorNatIso C).symm

variable (A B : C) {X X' Y Y' Z : C}
variable [Closed A]

/-- This is the internal hom `A ⟶[C] -`.
-/
/-
**CategoryTheory.ihom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：ihom : C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the internal hom `A ⟶[C] -`.
-/
def ihom : C ⥤ C :=
  Closed.rightAdj (X := A)

namespace ihom

/-- The adjunction between `A ⊗ -` and `A ⟹ -`. -/
/-
**CategoryTheory.ihom.adjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ihom`
。
形式化陈述：adjunction : tensorLeft A ⊣ ihom A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between `A ⊗ -` and `A ⟹ -`.
-/
def adjunction : tensorLeft A ⊣ ihom A :=
  Closed.adj
/-
**CategoryTheory.ihom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ihom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (tensorLeft A).IsLeftAdjoint :=
  (ihom.adjunction A).isLeftAdjoint
/-
**CategoryTheory.ihom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ihom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ihom A).IsRightAdjoint :=
  (ihom.adjunction A).isRightAdjoint

/-- The evaluation natural transformation. -/
/-
**CategoryTheory.ihom.ev** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ihom`。
形式化陈述：ev : ihom A ⋙ tensorLeft A ⟶ 𝟭 C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation natural transformation.
-/
def ev : ihom A ⋙ tensorLeft A ⟶ 𝟭 C :=
  (ihom.adjunction A).counit

/-- The coevaluation natural transformation. -/
/-
**CategoryTheory.ihom.coev** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ihom`。
形式化陈述：coev : 𝟭 C ⟶ tensorLeft A ⋙ ihom A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coevaluation natural transformation.
-/
def coev : 𝟭 C ⟶ tensorLeft A ⋙ ihom A :=
  (ihom.adjunction A).unit

@[simp]
/-
**CategoryTheory.ihom.ihom_adjunction_counit** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.ihom`。
形式化陈述：ihom_adjunction_counit : (ihom.adjunction A).counit = ev A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ihom_adjunction_counit : (ihom.adjunction A).counit = ev A :=
  rfl

@[simp]
/-
**CategoryTheory.ihom.ihom_adjunction_unit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ihom`。
形式化陈述：ihom_adjunction_unit : (ihom.adjunction A).unit = coev A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ihom_adjunction_unit : (ihom.adjunction A).unit = coev A :=
  rfl

set_option backward.isDefEq.respectTransparency false in -- Needed in DayConvolution/Closed.lean
@[reassoc (attr := simp)]
/-
**CategoryTheory.ihom.ev_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ih
om`。
形式化陈述：ev_naturality {X Y : C} (f : X ⟶ Y) : A ◁ (ihom A).map f ≫ (ev A).app Y = 
(ev A).app X ≫ f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem ev_naturality {X Y : C} (f : X ⟶ Y) :
    A ◁ (ihom A).map f ≫ (ev A).app Y = (ev A).app X ≫ f :=
  (ev A).naturality f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ihom.coev_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
ihom`。
形式化陈述：coev_naturality {X Y : C} (f : X ⟶ Y) : f ≫ (coev A).app Y = (coev A).app 
X ≫ (ihom A).map (A ◁ f)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem coev_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (coev A).app Y = (coev A).app X ≫ (ihom A).map (A ◁ f) :=
  (coev A).naturality f

set_option quotPrecheck false in
/-- `A ⟶[C] B` denotes the internal hom from `A` to `B` -/
notation A " ⟶[" C "] " B:10 => (@ihom C _ _ A _).obj B

@[reassoc (attr := simp)]
/-
**CategoryTheory.ihom.ev_coev** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ihom`。
形式化陈述：ev_coev : (A ◁ (coev A).app B) ≫ (ev A).app (A otimes B) = 𝟙 (A otimes B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
-/
theorem ev_coev : (A ◁ (coev A).app B) ≫ (ev A).app (A ⊗ B) = 𝟙 (A ⊗ B) :=
  (ihom.adjunction A).left_triangle_components _

@[reassoc (attr := simp)]
/-
**CategoryTheory.ihom.coev_ev** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ihom`。
形式化陈述：coev_ev : (coev A).app (A ⟶[C] B) ≫ (ihom A).map ((ev A).app B) = 𝟙 (A ⟶[C
] B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
theorem coev_ev : (coev A).app (A ⟶[C] B) ≫ (ihom A).map ((ev A).app B) = 𝟙 (A ⟶[C] B) :=
  Adjunction.right_triangle_components (ihom.adjunction A) _

end ihom

open CategoryTheory.Limits

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesColimits (tensorLeft A) :=
  (ihom.adjunction A).leftAdjoint_preservesColimits

variable {A}

-- Wrap these in a namespace so we don't clash with the core versions.
namespace MonoidalClosed

/-- Currying in a monoidal closed category. -/
/-
**CategoryTheory.MonoidalClosed.curry** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
MonoidalClosed`。
形式化陈述：curry : (A otimes Y ⟶ X) -> (Y ⟶ A ⟶[C] X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Currying in a monoidal closed category.
-/
def curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟶[C] X) :=
  (ihom.adjunction A).homEquiv _ _

/-- Uncurrying in a monoidal closed category. -/
/-
**CategoryTheory.MonoidalClosed.uncurry** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.MonoidalClosed`。
形式化陈述：uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Uncurrying in a monoidal closed category.
-/
def uncurry : (Y ⟶ A ⟶[C] X) → (A ⊗ Y ⟶ X) :=
  ((ihom.adjunction A).homEquiv _ _).symm
/-
**CategoryTheory.MonoidalClosed.homEquiv_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MonoidalClosed`。
形式化陈述：homEquiv_apply_eq (f : A otimes Y ⟶ X) : (ihom.adjunction A).homEquiv _ _ 
f = curry f
参数：f : A otimes Y ⟶ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homEquiv_apply_eq (f : A ⊗ Y ⟶ X) : (ihom.adjunction A).homEquiv _ _ f = curry f :=
  rfl
/-
**CategoryTheory.MonoidalClosed.homEquiv_symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MonoidalClosed`。
形式化陈述：homEquiv_symm_apply_eq (f : Y ⟶ A ⟶[C] X) : ((ihom.adjunction A).homEquiv 
_ _).symm f = uncurry f
参数：f : Y ⟶ A ⟶[C] X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem homEquiv_symm_apply_eq (f : Y ⟶ A ⟶[C] X) :
    ((ihom.adjunction A).homEquiv _ _).symm f = uncurry f :=
  rfl

@[reassoc]
/-
**CategoryTheory.MonoidalClosed.curry_natural_left** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MonoidalClosed`。
形式化陈述：curry_natural_left (f : X ⟶ X') (g : A otimes X' ⟶ Y) : curry (_ ◁ f ≫ g) 
= f ≫ curry g
参数：f : X ⟶ X'；g : A otimes X' ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left`：homEquiv_naturality_
left (f : X' ⟶ X) (g : F.obj X ⟶ Y) : (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (a
dj.homEquiv X Y) g
-/
theorem curry_natural_left (f : X ⟶ X') (g : A ⊗ X' ⟶ Y) : curry (_ ◁ f ≫ g) = f ≫ curry g :=
  Adjunction.homEquiv_naturality_left _ _ _

@[reassoc]
/-
**CategoryTheory.MonoidalClosed.curry_natural_right** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MonoidalClosed`。
形式化陈述：curry_natural_right (f : A otimes X ⟶ Y) (g : Y ⟶ Y') : curry (f ≫ g) = cu
rry f ≫ (ihom _).map g
参数：f : A otimes X ⟶ Y；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_right`：homEquiv_naturality
_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') : (adj.homEquiv X Y') (f ≫ g) = (adj.homEq
uiv X Y) f ≫ G.map g
-/
theorem curry_natural_right (f : A ⊗ X ⟶ Y) (g : Y ⟶ Y') :
    curry (f ≫ g) = curry f ≫ (ihom _).map g :=
  Adjunction.homEquiv_naturality_right _ _ _

@[reassoc]
/-
**CategoryTheory.MonoidalClosed.uncurry_natural_right** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalClosed`。
形式化陈述：uncurry_natural_right (f : X ⟶ A ⟶[C] Y) (g : Y ⟶ Y') : uncurry (f ≫ (ihom
 _).map g) = uncurry f ≫ g
参数：f : X ⟶ A ⟶[C] Y；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_right_symm`：homEquiv_natur
ality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') : (adj.homEquiv X Y').symm (f ≫ 
G.map g) = (adj.homEquiv X Y).symm f ≫ g
-/
theorem uncurry_natural_right (f : X ⟶ A ⟶[C] Y) (g : Y ⟶ Y') :
    uncurry (f ≫ (ihom _).map g) = uncurry f ≫ g :=
  Adjunction.homEquiv_naturality_right_symm _ _ _

@[reassoc]
/-
**CategoryTheory.MonoidalClosed.uncurry_natural_left** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MonoidalClosed`。
形式化陈述：uncurry_natural_left (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) : uncurry (f ≫ g) = 
_ ◁ f ≫ uncurry g
参数：f : X ⟶ X'；g : X' ⟶ A ⟶[C] Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left_symm`：homEquiv_natura
lity_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) : (adj.homEquiv X' Y).symm (f ≫ g)
 = F.map f ≫ (adj.homEquiv X Y).symm g
-/
theorem uncurry_natural_left (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) :
    uncurry (f ≫ g) = _ ◁ f ≫ uncurry g :=
  Adjunction.homEquiv_naturality_left_symm _ _ _

@[simp]
/-
**CategoryTheory.MonoidalClosed.uncurry_curry** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.MonoidalClosed`。
形式化陈述：uncurry_curry (f : A otimes X ⟶ Y) : uncurry (curry f) = f
参数：f : A otimes X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem uncurry_curry (f : A ⊗ X ⟶ Y) : uncurry (curry f) = f :=
  (Closed.adj.homEquiv _ _).left_inv f

@[simp]
/-
**CategoryTheory.MonoidalClosed.curry_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.MonoidalClosed`。
形式化陈述：curry_uncurry (f : X ⟶ A ⟶[C] Y) : curry (uncurry f) = f
参数：f : X ⟶ A ⟶[C] Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem curry_uncurry (f : X ⟶ A ⟶[C] Y) : curry (uncurry f) = f :=
  (Closed.adj.homEquiv _ _).right_inv f
/-
**CategoryTheory.MonoidalClosed.curry_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.MonoidalClosed`。
形式化陈述：curry_eq_iff (f : A otimes Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : curry f = g ↔ f = u
ncurry g
参数：f : A otimes Y ⟶ X；g : Y ⟶ A ⟶[C] X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.homEquiv_apply_eq`：homEquiv_apply_eq {A : C} {
B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) : adj.homEquiv A B f = g ↔ f = (adj.h
omEquiv A B).symm g
-/
theorem curry_eq_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : curry f = g ↔ f = uncurry g :=
  Adjunction.homEquiv_apply_eq (ihom.adjunction A) f g
/-
**CategoryTheory.MonoidalClosed.eq_curry_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.MonoidalClosed`。
形式化陈述：eq_curry_iff (f : A otimes Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : g = curry f ↔ uncur
ry g = f
参数：f : A otimes Y ⟶ X；g : Y ⟶ A ⟶[C] X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.eq_homEquiv_apply`：eq_homEquiv_apply {A : C} {
B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) : g = adj.homEquiv A B f ↔ (adj.homEq
uiv A B).symm g = f
-/
theorem eq_curry_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : g = curry f ↔ uncurry g = f :=
  Adjunction.eq_homEquiv_apply (ihom.adjunction A) f g

-- I don't think these two should be simp.
/-
**CategoryTheory.MonoidalClosed.uncurry_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.MonoidalClosed`。
形式化陈述：uncurry_eq (g : Y ⟶ A ⟶[C] X) : uncurry g = (A ◁ g) ≫ (ihom.ev A).app X
参数：g : Y ⟶ A ⟶[C] X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uncurry_eq (g : Y ⟶ A ⟶[C] X) : uncurry g = (A ◁ g) ≫ (ihom.ev A).app X := by
  rfl
/-
**CategoryTheory.MonoidalClosed.curry_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.MonoidalClosed`。
形式化陈述：curry_eq (g : A otimes Y ⟶ X) : curry g = (ihom.coev A).app Y ≫ (ihom A).m
ap g
参数：g : A otimes Y ⟶ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curry_eq (g : A ⊗ Y ⟶ X) : curry g = (ihom.coev A).app Y ≫ (ihom A).map g :=
  rfl
/-
**CategoryTheory.MonoidalClosed.curry_injective** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MonoidalClosed`。
形式化陈述：curry_injective : Function.Injective (curry : (A otimes Y ⟶ X) -> (Y ⟶ A ⟶
[C] X))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem curry_injective : Function.Injective (curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟶[C] X)) :=
  (Closed.adj.homEquiv _ _).injective
/-
**CategoryTheory.MonoidalClosed.uncurry_injective** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MonoidalClosed`。
形式化陈述：uncurry_injective : Function.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A oti
mes Y ⟶ X))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem uncurry_injective : Function.Injective (uncurry : (Y ⟶ A ⟶[C] X) → (A ⊗ Y ⟶ X)) :=
  (Closed.adj.homEquiv _ _).symm.injective

variable (A X)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.MonoidalClosed.uncurry_id_eq_ev** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MonoidalClosed`。
形式化陈述：uncurry_id_eq_ev : uncurry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_eq`：uncurry_eq (g : Y ⟶ A ⟶[C] X) 
: uncurry g = (A ◁ g) ≫ (ihom.ev A).app X
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uncurry_id_eq_ev : uncurry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X := by
  simp [uncurry_eq]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalClosed.curry_id_eq_coev** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MonoidalClosed`。
形式化陈述：curry_id_eq_coev : curry (𝟙 _) = (ihom.coev A).app X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.curry_eq`：curry_eq (g : A otimes Y ⟶ X) : 
curry g = (ihom.coev A).app Y ≫ (ihom A).map g
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem curry_id_eq_coev : curry (𝟙 _) = (ihom.coev A).app X := by
  rw [curry_eq, (ihom A).map_id (A ⊗ _)]
  apply comp_id

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalClosed.whiskerLeft_curry_ihom_ev_app** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.MonoidalClosed`。
形式化陈述：whiskerLeft_curry_ihom_ev_app (g : A otimes Y ⟶ X) : A ◁ curry g ≫ (ihom.e
v A).app X = g
参数：g : A otimes Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ihom.ev_naturality`：ev_naturality {X Y : C} (f : X ⟶ Y) :
 A ◁ (ihom A).map f ≫ (ev A).app Y = (ev A).app X ≫ f
· 使用定理 `CategoryTheory.ihom.ev_coev_assoc`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] (A B : C)   [in
st_2 : CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_curry_ihom_ev_app (g : A ⊗ Y ⟶ X) :
    A ◁ curry g ≫ (ihom.ev A).app X = g := by
  simp [curry_eq]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalClosed.uncurry_ihom_map** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MonoidalClosed`。
形式化陈述：uncurry_ihom_map (g : Y ⟶ Y') : uncurry ((ihom A).map g) = (ihom.ev A).app
 Y ≫ g
参数：g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalClosed.curry_injective`：curry_injective : Functio
n.Injective (curry : (A otimes Y ⟶ X) -> (Y ⟶ A ⟶[C] X))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.curry_uncurry`：curry_uncurry (f : X ⟶ A ⟶[
C] Y) : curry (uncurry f) = f
· 使用定理 `CategoryTheory.MonoidalClosed.curry_natural_right`：curry_natural_right (
f : A otimes X ⟶ Y) (g : Y ⟶ Y') : curry (f ≫ g) = curry f ≫ (ihom _).map g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_id_eq_ev`：uncurry_id_eq_ev : uncur
ry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem uncurry_ihom_map (g : Y ⟶ Y') :
    uncurry ((ihom A).map g) = (ihom.ev A).app Y ≫ g := by
  apply curry_injective
  rw [curry_uncurry, curry_natural_right, ← uncurry_id_eq_ev, curry_uncurry, id_comp]

/-- The internal hom out of the unit is naturally isomorphic to the identity functor. -/
/-
**CategoryTheory.MonoidalClosed.unitNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MonoidalClosed`。
形式化陈述：unitNatIso [Closed (𝟙_ C)] : 𝟭 C ≅ ihom (𝟙_ C)
参数：𝟙_ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The internal hom out of the unit is naturally isomorphic to the identity functor
.
-/
def unitNatIso [Closed (𝟙_ C)] : 𝟭 C ≅ ihom (𝟙_ C) :=
  conjugateIsoEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C)

/-- The internal hom object from the unit to any object is isomorphic to that object.
The typeclass argument is explicit: any instance can be used. -/
/-
**CategoryTheory.MonoidalClosed.unitIsoSelf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.MonoidalClosed`。
形式化陈述：unitIsoSelf [Closed (𝟙_ C)] : ((𝟙_ C) ⟶[C] X) ≅ X
参数：𝟙_ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The internal hom object from the unit to any object is isomorphic to that object
.
The typeclass argument is explicit: any instance can be used.
-/
def unitIsoSelf [Closed (𝟙_ C)] : ((𝟙_ C) ⟶[C] X) ≅ X :=
  (unitNatIso.app X).symm

section Pre

variable {A B}
variable [Closed B]

/-- Pre-compose an internal hom with an external hom. -/
/-
**CategoryTheory.MonoidalClosed.pre** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mo
noidalClosed`。
形式化陈述：pre (f : B ⟶ A) : ihom A ⟶ ihom B
参数：f : B ⟶ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pre-compose an internal hom with an external hom.
-/
def pre (f : B ⟶ A) : ihom A ⟶ ihom B :=
  conjugateEquiv (ihom.adjunction _) (ihom.adjunction _) ((tensoringLeft C).map f)

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalClosed.id_tensor_pre_app_comp_ev** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.MonoidalClosed`。
形式化陈述：id_tensor_pre_app_comp_ev (f : B ⟶ A) (X : C) : B ◁ (pre f).app X ≫ (ihom.
ev B).app X = f ▷ (A ⟶[C] X) ≫ (ihom.ev A).app X
参数：f : B ⟶ A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.conjugateEquiv_counit`：conjugateEquiv_counit (α : L₂ ⟶ L₁
) (d : D) : L₂.map ((conjugateEquiv adj₁ adj₂ α).app _) ≫ adj₂.counit.app d = α.
app _ ≫ adj₁.counit.app d
-/
theorem id_tensor_pre_app_comp_ev (f : B ⟶ A) (X : C) :
    B ◁ (pre f).app X ≫ (ihom.ev B).app X = f ▷ (A ⟶[C] X) ≫ (ihom.ev A).app X :=
  conjugateEquiv_counit _ _ ((tensoringLeft C).map f) X

@[simp]
/-
**CategoryTheory.MonoidalClosed.uncurry_pre** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.MonoidalClosed`。
形式化陈述：uncurry_pre (f : B ⟶ A) (X : C) : MonoidalClosed.uncurry ((pre f).app X) =
 f ▷ _ ≫ (ihom.ev A).app X
参数：f : B ⟶ A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_eq`：uncurry_eq (g : Y ⟶ A ⟶[C] X) 
: uncurry g = (A ◁ g) ≫ (ihom.ev A).app X
· 使用定理 `CategoryTheory.MonoidalClosed.id_tensor_pre_app_comp_ev`：id_tensor_pre_a
pp_comp_ev (f : B ⟶ A) (X : C) : B ◁ (pre f).app X ≫ (ihom.ev B).app X = f ▷ (A 
⟶[C] X) ≫ (ihom.ev A).app X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uncurry_pre (f : B ⟶ A) (X : C) :
    MonoidalClosed.uncurry ((pre f).app X) = f ▷ _ ≫ (ihom.ev A).app X := by
  simp [uncurry_eq]

@[reassoc]
/-
**CategoryTheory.MonoidalClosed.curry_pre_app** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MonoidalClosed`。
形式化陈述：curry_pre_app (f : B ⟶ A) {X Y : C} (g : A otimes Y ⟶ X) : curry g ≫ (pre 
f).app X = curry (f ▷ _ ≫ g)
参数：f : B ⟶ A；g : A otimes Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_injective`：uncurry_injective : Fun
ction.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_eq`：uncurry_eq (g : Y ⟶ A ⟶[C] X) 
: uncurry g = (A ◁ g) ≫ (ihom.ev A).app X
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalClosed.id_tensor_pre_app_comp_ev`：id_tensor_pre_a
pp_comp_ev (f : B ⟶ A) (X : C) : B ◁ (pre f).app X ≫ (ihom.ev B).app X = f ▷ (A 
⟶[C] X) ≫ (ihom.ev A).app X
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用引理 `CategoryTheory.MonoidalClosed.whiskerLeft_curry_ihom_ev_app`：whiskerLeft
_curry_ihom_ev_app (g : A otimes Y ⟶ X) : A ◁ curry g ≫ (ihom.ev A).app X = g
-/
lemma curry_pre_app (f : B ⟶ A) {X Y : C} (g : A ⊗ Y ⟶ X) :
    curry g ≫ (pre f).app X = curry (f ▷ _ ≫ g) := uncurry_injective (by
  rw [uncurry_curry, uncurry_eq, MonoidalCategory.whiskerLeft_comp, assoc,
    id_tensor_pre_app_comp_ev, whisker_exchange_assoc, whiskerLeft_curry_ihom_ev_app])

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalClosed.coev_app_comp_pre_app** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalClosed`。
形式化陈述：coev_app_comp_pre_app (f : B ⟶ A) : (ihom.coev A).app X ≫ (pre f).app (A o
times X) = (ihom.coev B).app X ≫ (ihom B).map (f ▷ _)
参数：f : B ⟶ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.unit_conjugateEquiv`：unit_conjugateEquiv (α : L₂ ⟶ L₁) (c
 : C) : adj₁.unit.app _ ≫ (conjugateEquiv adj₁ adj₂ α).app _ = adj₂.unit.app c ≫
 R₂.map (α.app _)
-/
theorem coev_app_comp_pre_app (f : B ⟶ A) :
    (ihom.coev A).app X ≫ (pre f).app (A ⊗ X) = (ihom.coev B).app X ≫ (ihom B).map (f ▷ _) :=
  unit_conjugateEquiv _ _ ((tensoringLeft C).map f) X

@[reassoc]
/-
**CategoryTheory.MonoidalClosed.uncurry_pre_app** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MonoidalClosed`。
形式化陈述：uncurry_pre_app (f : Y ⟶ A ⟶[C] X) (g : B ⟶ A) : uncurry (f ≫ (pre g).app 
X) = g ▷ _ ≫ uncurry f
参数：f : Y ⟶ A ⟶[C] X；g : B ⟶ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalClosed.curry_injective`：curry_injective : Functio
n.Injective (curry : (A otimes Y ⟶ X) -> (Y ⟶ A ⟶[C] X))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.curry_uncurry`：curry_uncurry (f : X ⟶ A ⟶[
C] Y) : curry (uncurry f) = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MonoidalClosed.curry_pre_app`：curry_pre_app (f : B ⟶ A) {
X Y : C} (g : A otimes Y ⟶ X) : curry g ≫ (pre f).app X = curry (f ▷ _ ≫ g)
-/
lemma uncurry_pre_app (f : Y ⟶ A ⟶[C] X) (g : B ⟶ A) :
    uncurry (f ≫ (pre g).app X) = g ▷ _ ≫ uncurry f :=
  curry_injective (by
    rw [curry_uncurry, ← curry_pre_app, curry_uncurry])

@[simp]
/-
**CategoryTheory.MonoidalClosed.pre_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.MonoidalClosed`。
形式化陈述：pre_id (A : C) [Closed A] : pre (𝟙 A) = 𝟙 _
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.pre.eq_1`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] {A B : C} 
  [inst_2 : CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.conjugateEquiv_id`：conjugateEquiv_id : conjugateEquiv adj
₁ adj₁ (𝟙 _) = 𝟙 _
-/
theorem pre_id (A : C) [Closed A] : pre (𝟙 A) = 𝟙 _ := by
  rw [pre, Functor.map_id]
  apply conjugateEquiv_id

@[simp]
/-
**CategoryTheory.MonoidalClosed.pre_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.MonoidalClosed`。
形式化陈述：pre_map {A₁ A₂ A₃ : C} [Closed A₁] [Closed A₂] [Closed A₃] (f : A₁ ⟶ A₂) (
g : A₂ ⟶ A₃) : pre (f ≫ g) = pre g ≫ pre f
参数：f : A₁ ⟶ A₂；g : A₂ ⟶ A₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.pre.eq_1`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] {A B : C} 
  [inst_2 : CategoryTheory.C…
· 使用定理 `CategoryTheory.conjugateEquiv_comp`：conjugateEquiv_comp (α : L₂ ⟶ L₁) (β
 : L₃ ⟶ L₂) : conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ β = conjugat
eEquiv adj₁ adj₃ (β ≫ α)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem pre_map {A₁ A₂ A₃ : C} [Closed A₁] [Closed A₂] [Closed A₃] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    pre (f ≫ g) = pre g ≫ pre f := by
  rw [pre, pre, pre, conjugateEquiv_comp, (tensoringLeft C).map_comp]
/-
**CategoryTheory.MonoidalClosed.pre_comm_ihom_map** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MonoidalClosed`。
形式化陈述：pre_comm_ihom_map {W X Y Z : C} [Closed W] [Closed X] (f : W ⟶ X) (g : Y ⟶
 Z) : (pre f).app Y ≫ (ihom W).map g = (ihom X).map g ≫ (pre f).app Z
参数：f : W ⟶ X；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pre_comm_ihom_map {W X Y Z : C} [Closed W] [Closed X] (f : W ⟶ X) (g : Y ⟶ Z) :
    (pre f).app Y ≫ (ihom W).map g = (ihom X).map g ≫ (pre f).app Z := by simp

end Pre

/-- The internal hom functor given by the monoidal closed structure. -/
@[simps]
/-
**CategoryTheory.MonoidalClosed.internalHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.MonoidalClosed`。
形式化陈述：internalHom [MonoidalClosed C] : Cᵒᵖ ⥤ C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The internal hom functor given by the monoidal closed structure.
-/
def internalHom [MonoidalClosed C] : Cᵒᵖ ⥤ C ⥤ C where
  obj X := ihom X.unop
  map f := pre f.unop
/-
**CategoryTheory.MonoidalClosed.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monoi
dalClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MonoidalClosed C] (X : Cᵒᵖ) : (internalHom.obj X).IsRightAdjoint := by
  bdsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The parametrized adjunction between `curriedTensor C : C ⥤ C ⥤ C`
and `internalHom : Cᵒᵖ ⥤ C ⥤ C` -/
@[simps!]
/-
**CategoryTheory.MonoidalClosed.internalHomAdjunction** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.MonoidalClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The parametrized adjunction between `curriedTensor C : C ⥤ C ⥤ C`
and `internalHom : Cᵒᵖ ⥤ C ⥤ C`
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
/-
**CategoryTheory.MonoidalClosed.ofEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.MonoidalClosed`。
形式化陈述：ofEquiv : MonoidalClosed C where closed X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport the property of being monoidal closed across a monoidal equivalence of
 categories
-/
noncomputable def ofEquiv : MonoidalClosed C where
  closed X :=
    { rightAdj := F ⋙ ihom (F.obj X) ⋙ G
      adj := (adj.comp ((ihom.adjunction (F.obj X)).comp
          adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft
            (Iso.compInverseIso (H := adj.toEquivalence) (Functor.Monoidal.commTensorLeft F X)) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Suppose we have a monoidal equivalence `F : C ≌ D`, with `D` monoidal closed. We can pull the
monoidal closed instance back along the equivalence. For `X, Y, Z : C`, this lemma describes the
resulting currying map `Hom(X ⊗ Y, Z) → Hom(Y, (X ⟶[C] Z))`. (`X ⟶[C] Z` is defined to be
`F⁻¹(F(X) ⟶[D] F(Z))`, so currying in `C` is given by essentially conjugating currying in
`D` by `F.`) -/
/-
**CategoryTheory.MonoidalClosed.ofEquiv_curry_def** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MonoidalClosed`。
形式化陈述：ofEquiv_curry_def {X Y Z : C} (f : X otimes Y ⟶ Z) : letI
参数：f : X otimes Y ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoFunctorCounitOfIsEquivalence`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.homEquiv_ofNatIsoLeft_apply`：homEquiv_ofNatIso
Left_apply {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) {X : C} {Y : D}
 (f : G.obj X ⟶ Y) : (ofNatIsoLeft adj iso)…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用引理 `CategoryTheory.Adjunction.comp_homEquiv`：comp_homEquiv : (adj₁.comp adj₂
).homEquiv = fun _ _ => Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _)

--- 原说明 ---
Suppose we have a monoidal equivalence `F : C ≌ D`, with `D` monoidal closed. We
 can pull the
monoidal closed instance back along the equivalence. For `X, Y, Z : C`, this lem
ma describes the
resulting currying map `Hom(X ⊗ Y, Z) → Hom(Y, (X ⟶[C] Z))`. (`X ⟶[C] Z` is defi
ned to be
`F⁻¹(F(X) ⟶[D] F(Z))`, so currying in `C` is given by essentially conjugating cu
rrying in
`D` by `F.`)
-/
theorem ofEquiv_curry_def {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    letI := ofEquiv F adj
    MonoidalClosed.curry f =
      adj.homEquiv Y ((ihom (F.obj X)).obj (F.obj Z))
        (MonoidalClosed.curry (adj.toEquivalence.symm.toAdjunction.homEquiv (F.obj X ⊗ F.obj Y) Z
        ((Iso.compInverseIso (H := adj.toEquivalence)
          (Functor.Monoidal.commTensorLeft F X)).hom.app Y ≫ f))) := by
  -- This whole proof used to be `rfl` before https://github.com/leanprover-community/mathlib4/pull/16317.
  change ((adj.comp ((ihom.adjunction (F.obj X)).comp
      adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft _).homEquiv _ _ _ = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  dsimp
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Suppose we have a monoidal equivalence `F : C ≌ D`, with `D` monoidal closed. We can pull the
monoidal closed instance back along the equivalence. For `X, Y, Z : C`, this lemma describes the
resulting uncurrying map `Hom(Y, (X ⟶[C] Z)) → Hom(X ⊗ Y ⟶ Z)`. (`X ⟶[C] Z` is
defined to be `F⁻¹(F(X) ⟶[D] F(Z))`, so uncurrying in `C` is given by essentially conjugating
uncurrying in `D` by `F.`) -/
/-
**CategoryTheory.MonoidalClosed.ofEquiv_uncurry_def** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MonoidalClosed`。
形式化陈述：ofEquiv_uncurry_def {X Y Z : C} : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoFunctorCounitOfIsEquivalence`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.homEquiv_ofNatIsoLeft_symm_apply`：homEquiv_ofN
atIsoLeft_symm_apply {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) {X : 
C} {Y : D} (f : X ⟶ H.obj Y) : ((ofNatIsoLeft ad…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用引理 `CategoryTheory.Adjunction.comp_homEquiv`：comp_homEquiv : (adj₁.comp adj₂
).homEquiv = fun _ _ => Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _)

--- 原说明 ---
Suppose we have a monoidal equivalence `F : C ≌ D`, with `D` monoidal closed. We
 can pull the
monoidal closed instance back along the equivalence. For `X, Y, Z : C`, this lem
ma describes the
resulting uncurrying map `Hom(Y, (X ⟶[C] Z)) → Hom(X ⊗ Y ⟶ Z)`. (`X ⟶[C] Z` is
defined to be `F⁻¹(F(X) ⟶[D] F(Z))`, so uncurrying in `C` is given by essentiall
y conjugating
uncurrying in `D` by `F.`)
-/
theorem ofEquiv_uncurry_def {X Y Z : C} :
    letI := ofEquiv F adj
    ∀ (f : Y ⟶ (ihom X).obj Z), MonoidalClosed.uncurry f =
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
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

end OfEquiv

-- A closed monoidal category C is always enriched over itself.
-- This section contains the necessary definitions and equalities to endow C with
-- the structure of a C-category, while the instance itself is defined in `Closed/Enrichment`.
-- In particular, we only assume the necessary instances of `Closed x`, rather than assuming
-- C comes with an instance of `MonoidalClosed`
section Enriched

/-- The C-identity morphism
  `𝟙_ C ⟶ hom(x, x)`
used to equip `C` with the structure of a `C`-category -/
/-
**CategoryTheory.MonoidalClosed.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mon
oidalClosed`。
形式化陈述：id (x : C) [Closed x] : 𝟙_ C ⟶ (ihom x).obj x
参数：x : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The C-identity morphism
  `𝟙_ C ⟶ hom(x, x)`
used to equip `C` with the structure of a `C`-category
-/
def id (x : C) [Closed x] : 𝟙_ C ⟶ (ihom x).obj x := curry (ρ_ x).hom

/-- The *uncurried* composition morphism
  `x ⊗ (hom(x, y) ⊗ hom(y, z)) ⟶ (x ⊗ hom(x, y)) ⊗ hom(y, z) ⟶ y ⊗ hom(y, z) ⟶ z`.
The `C`-composition morphism will be defined as the adjoint transpose of this map. -/
/-
**CategoryTheory.MonoidalClosed.compTranspose** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MonoidalClosed`。
形式化陈述：compTranspose (x y z : C) [Closed x] [Closed y] : x otimes (ihom x).obj y 
otimes (ihom y).obj z ⟶ z
参数：x y z : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The *uncurried* composition morphism
  `x ⊗ (hom(x, y) ⊗ hom(y, z)) ⟶ (x ⊗ hom(x, y)) ⊗ hom(y, z) ⟶ y ⊗ hom(y, z) ⟶ z
`.
The `C`-composition morphism will be defined as the adjoint transpose of this ma
p.
-/
def compTranspose (x y z : C) [Closed x] [Closed y] : x ⊗ (ihom x).obj y ⊗ (ihom y).obj z ⟶ z :=
  (α_ x ((ihom x).obj y) ((ihom y).obj z)).inv ≫
    (ihom.ev x).app y ▷ ((ihom y).obj z) ≫ (ihom.ev y).app z

/-- The `C`-composition morphism
  `hom(x, y) ⊗ hom(y, z) ⟶ hom(x, z)`
used to equip `C` with the structure of a `C`-category -/
/-
**CategoryTheory.MonoidalClosed.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.M
onoidalClosed`。
形式化陈述：comp (x y z : C) [Closed x] [Closed y] : (ihom x).obj y otimes (ihom y).ob
j z ⟶ (ihom x).obj z
参数：x y z : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `C`-composition morphism
  `hom(x, y) ⊗ hom(y, z) ⟶ hom(x, z)`
used to equip `C` with the structure of a `C`-category
-/
def comp (x y z : C) [Closed x] [Closed y] : (ihom x).obj y ⊗ (ihom y).obj z ⟶ (ihom x).obj z :=
  curry (compTranspose x y z)

/-- Unfold the definition of `id`.
This exists to streamline the proofs of `MonoidalClosed.id_comp` and `MonoidalClosed.comp_id` -/
/-
**CategoryTheory.MonoidalClosed.id_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
MonoidalClosed`。
形式化陈述：id_eq (x : C) [Closed x] : id x = curry (ρ_ x).hom
参数：x : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unfold the definition of `id`.
This exists to streamline the proofs of `MonoidalClosed.id_comp` and `MonoidalCl
osed.comp_id`
-/
lemma id_eq (x : C) [Closed x] : id x = curry (ρ_ x).hom := rfl

/-- Unfold the definition of `compTranspose`.
This exists to streamline the proof of `MonoidalClosed.assoc` -/
/-
**CategoryTheory.MonoidalClosed.compTranspose_eq** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.MonoidalClosed`。
形式化陈述：compTranspose_eq (x y z : C) [Closed x] [Closed y] : compTranspose x y z =
 (α_ _ _ _).inv ≫ (ihom.ev x).app y ▷ _ ≫ (ihom.ev y).app z
参数：x y z : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unfold the definition of `compTranspose`.
This exists to streamline the proof of `MonoidalClosed.assoc`
-/
lemma compTranspose_eq (x y z : C) [Closed x] [Closed y] :
    compTranspose x y z = (α_ _ _ _).inv ≫ (ihom.ev x).app y ▷ _ ≫ (ihom.ev y).app z :=
  rfl

/-- Unfold the definition of `comp`.
This exists to streamline the proof of `MonoidalClosed.assoc` -/
/-
**CategoryTheory.MonoidalClosed.comp_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.MonoidalClosed`。
形式化陈述：comp_eq (x y z : C) [Closed x] [Closed y] : comp x y z = curry (compTransp
ose x y z)
参数：x y z : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unfold the definition of `comp`.
This exists to streamline the proof of `MonoidalClosed.assoc`
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
/-
**CategoryTheory.MonoidalClosed.id_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.MonoidalClosed`。
形式化陈述：id_comp (x y : C) [Closed x] : (fun_ ((ihom x).obj y)).inv ≫ id x ▷ _ ≫ co
mp x x y = 𝟙 _
参数：x y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_injective`：uncurry_injective : Fun
ction.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_natural_left`：uncurry_natural_left
 (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) : uncurry (f ≫ g) = _ ◁ f ≫ uncurry g
· 使用引理 `CategoryTheory.MonoidalClosed.comp_eq`：comp_eq (x y z : C) [Closed x] [C
losed y] : comp x y z = curry (compTranspose x y z)
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
· 使用引理 `CategoryTheory.MonoidalClosed.id_eq`：id_eq (x : C) [Closed x] : id x = c
urry (ρ_ x).hom
· 使用引理 `CategoryTheory.MonoidalClosed.compTranspose_eq`：compTranspose_eq (x y z 
: C) [Closed x] [Closed y] : compTranspose x y z = (α_ _ _ _).inv ≫ (ihom.ev x).
app y ▷ _ ≫ (ihom.ev y).app z
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_middle_assoc`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheor
y.MonoidalCategory C] (X : C) {Y Y' : C}   (f : Y ⟶ Y') (Z :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_eq`：uncurry_eq (g : Y ⟶ A ⟶[C] X) 
: uncurry g = (A ◁ g) ≫ (ihom.ev A).app X
· 使用定理 `CategoryTheory.MonoidalCategory.triangle_assoc_comp_right_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoi
dalCategory C] (X Y : C) {Z : C}   (h : CategoryTheor…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_inv_hom_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] (X : C) {Y Z : C}   (f : Y ≅ Z) {Z_1 :…
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_id_eq_ev`：uncurry_id_eq_ev : uncur
ry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X

--- 原说明 ---
Left unitality of the enriched structure
-/
lemma id_comp (x y : C) [Closed x] :
    (λ_ ((ihom x).obj y)).inv ≫ id x ▷ _ ≫ comp x x y = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, comp_eq, uncurry_curry, id_eq, compTranspose_eq,
      associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, ← uncurry_eq,
      uncurry_curry, triangle_assoc_comp_right_assoc, whiskerLeft_inv_hom_assoc,
      uncurry_id_eq_ev _ _]

set_option backward.isDefEq.respectTransparency false in
/-- Right unitality of the enriched structure -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalClosed.comp_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.MonoidalClosed`。
形式化陈述：comp_id (x y : C) [Closed x] [Closed y] : (ρ_ ((ihom x).obj y)).inv ≫ _ ◁ 
id y ≫ comp x y y = 𝟙 _
参数：x y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_injective`：uncurry_injective : Fun
ction.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_natural_left`：uncurry_natural_left
 (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) : uncurry (f ≫ g) = _ ◁ f ≫ uncurry g
· 使用引理 `CategoryTheory.MonoidalClosed.comp_eq`：comp_eq (x y z : C) [Closed x] [C
losed y] : comp x y z = curry (compTranspose x y z)
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
· 使用引理 `CategoryTheory.MonoidalClosed.compTranspose_eq`：compTranspose_eq (x y z 
: C) [Closed x] [Closed y] : compTranspose x y z = (α_ _ _ _).inv ≫ (ihom.ev x).
app y ▷ _ ≫ (ihom.ev y).app z
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_right_assoc`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.MonoidalCategory C] (X Y : C)   {Z Z' : C} (f : Z ⟶ Z') {Z…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.rightUnitor_tensor_inv_assoc`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoidal
Category C] (X Y : C) {Z : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.MonoidalCategory.rightUnitor_inv_naturality_assoc`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mono
idalCategory C] {X X' : C}   (f : X ⟶ X') {Z : C}   (h…
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_id_eq_ev`：uncurry_id_eq_ev : uncur
ry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Right unitality of the enriched structure
-/
lemma comp_id (x y : C) [Closed x] [Closed y] :
    (ρ_ ((ihom x).obj y)).inv ≫ _ ◁ id y ≫ comp x y y = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, comp_eq, uncurry_curry, compTranspose_eq,
    associator_inv_naturality_right_assoc, ← rightUnitor_tensor_inv_assoc,
    whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc, ← uncurry_id_eq_ev y y]
  simp only [Functor.id_obj]
  rw [← uncurry_natural_left]
  simp [id_eq, uncurry_id_eq_ev]

set_option backward.isDefEq.respectTransparency false in
/-- Associativity of the enriched structure -/
@[reassoc]
/-
**CategoryTheory.MonoidalClosed.assoc** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
MonoidalClosed`。
形式化陈述：assoc (w x y z : C) [Closed w] [Closed x] [Closed y] : (α_ _ _ _).inv ≫ co
mp w x y ▷ _ ≫ comp w y z = _ ◁ comp x y z ≫ comp w x z
参数：w x y z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_injective`：uncurry_injective : Fun
ction.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_natural_left`：uncurry_natural_left
 (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) : uncurry (f ≫ g) = _ ◁ f ≫ uncurry g
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_middle_assoc`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheor
y.MonoidalCategory C] (X : C) {Y Y' : C}   (f : Y ⟶ Y') (Z :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_eq`：uncurry_eq (g : Y ⟶ A ⟶[C] X) 
: uncurry g = (A ◁ g) ≫ (ihom.ev A).app X
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_right_assoc`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.MonoidalCategory C] (X Y : C)   {Z Z' : C} (f : Z ⟶ Z') {Z…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv_assoc`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Associativity of the enriched structure
-/
lemma assoc (w x y z : C) [Closed w] [Closed x] [Closed y] :
    (α_ _ _ _).inv ≫ comp w x y ▷ _ ≫ comp w y z = _ ◁ comp x y z ≫ comp w x z := by
  apply uncurry_injective
  simp only [uncurry_natural_left, comp_eq]
  rw [uncurry_curry, uncurry_curry]; simp only [compTranspose_eq]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc]; dsimp
  rw [← uncurry_eq, uncurry_curry, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    ← uncurry_eq, uncurry_curry]
  simp

end Enriched

section OrdinaryEnriched

/-- The morphism `𝟙_ C ⟶ (ihom X).obj Y` corresponding to a morphism `X ⟶ Y`. -/
/-
**CategoryTheory.MonoidalClosed.curry'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.MonoidalClosed`。
形式化陈述：curry' {X Y : C} [Closed X] (f : X ⟶ Y) : 𝟙_ C ⟶ (ihom X).obj Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `𝟙_ C ⟶ (ihom X).obj Y` corresponding to a morphism `X ⟶ Y`.
-/
def curry' {X Y : C} [Closed X] (f : X ⟶ Y) : 𝟙_ C ⟶ (ihom X).obj Y :=
  curry ((ρ_ _).hom ≫ f)

/-- The morphism `X ⟶ Y` corresponding to a morphism `𝟙_ C ⟶ (ihom X).obj Y`. -/
/-
**CategoryTheory.MonoidalClosed.uncurry'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.MonoidalClosed`。
形式化陈述：uncurry' {X Y : C} [Closed X] (g : 𝟙_ C ⟶ (ihom X).obj Y) : X ⟶ Y
参数：g : 𝟙_ C ⟶ (ihom X).obj Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `X ⟶ Y` corresponding to a morphism `𝟙_ C ⟶ (ihom X).obj Y`.
-/
def uncurry' {X Y : C} [Closed X] (g : 𝟙_ C ⟶ (ihom X).obj Y) : X ⟶ Y :=
  (ρ_ _).inv ≫ uncurry g

/-- `curry'` and `uncurry'` are inverse bijections. -/
@[simp]
/-
**CategoryTheory.MonoidalClosed.curry'_uncurry'** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MonoidalClosed`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C] {X Y : C}   [inst_2 : CategoryTheory.Closed X] (g : 
CategoryTheory.MonoidalCategoryStruct.tensorUnit C ⟶ X ⟹ Y),   CategoryTheory.Mo
noidalClosed.curry' (CategoryTheory.MonoidalClosed.uncurry' g) = g
参数：g : CategoryTheory.MonoidalCategoryStruct.tensorUnit C ⟶ X ⟹ Y；CategoryTheory
.MonoidalClosed.uncurry' g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalClosed.curry_uncurry`：curry_uncurry (f : X ⟶ A ⟶[
C] Y) : curry (uncurry f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`curry'` and `uncurry'` are inverse bijections.
-/
lemma curry'_uncurry' {X Y : C} [Closed X] (g : 𝟙_ C ⟶ (ihom X).obj Y) :
    curry' (uncurry' g) = g := by
  simp [curry', uncurry']

/-- `curry'` and `uncurry'` are inverse bijections. -/
@[simp]
/-
**CategoryTheory.MonoidalClosed.uncurry'_curry'** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MonoidalClosed`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C] {X Y : C}   [inst_2 : CategoryTheory.Closed X] (f : 
X ⟶ Y),   CategoryTheory.MonoidalClosed.uncurry' (CategoryTheory.MonoidalClosed.
curry' f) = f
参数：f : X ⟶ Y；CategoryTheory.MonoidalClosed.curry' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`curry'` and `uncurry'` are inverse bijections.
-/
lemma uncurry'_curry' {X Y : C} [Closed X] (f : X ⟶ Y) :
    uncurry' (curry' f) = f := by
  simp [curry', uncurry']

/-- The bijection `(X ⟶ Y) ≃ (𝟙_ C ⟶ (ihom X).obj Y)` in a monoidal closed category. -/
@[simps]
/-
**CategoryTheory.MonoidalClosed.curryHomEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.MonoidalClosed`。
形式化陈述：curryHomEquiv' {X Y : C} [Closed X] : (X ⟶ Y) ≃ (𝟙_ C ⟶ (ihom X).obj Y) wh
ere toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(X ⟶ Y) ≃ (𝟙_ C ⟶ (ihom X).obj Y)` in a monoidal closed category.
-/
def curryHomEquiv' {X Y : C} [Closed X] :
    (X ⟶ Y) ≃ (𝟙_ C ⟶ (ihom X).obj Y) where
  toFun := curry'
  invFun := uncurry'
  left_inv _ := by simp
  right_inv _ := by simp
/-
**CategoryTheory.MonoidalClosed.curry'_injective** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MonoidalClosed`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C] {X Y : C}   [inst_2 : CategoryTheory.Closed X] {f f'
 : X ⟶ Y},   CategoryTheory.MonoidalClosed.curry' f = CategoryTheory.MonoidalClo
sed.curry' f' → f = f'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma curry'_injective {X Y : C} [Closed X] {f f' : X ⟶ Y} (h : curry' f = curry' f') :
    f = f' :=
  curryHomEquiv'.injective h
/-
**CategoryTheory.MonoidalClosed.uncurry'_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MonoidalClosed`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C] {X Y : C}   [inst_2 : CategoryTheory.Closed X] {f f'
 : CategoryTheory.MonoidalCategoryStruct.tensorUnit C ⟶ X ⟹ Y},   CategoryTheory
.MonoidalClosed.uncurry' f = CategoryTheory.MonoidalClosed.uncurry' f' → f = f'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma uncurry'_injective {X Y : C} [Closed X] {f f' : 𝟙_ C ⟶ (ihom X).obj Y}
    (h : uncurry' f = uncurry' f') : f = f' :=
  curryHomEquiv'.symm.injective h

@[simp]
/-
**CategoryTheory.MonoidalClosed.curry'_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.MonoidalClosed`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C] (X : C)   [inst_2 : CategoryTheory.Closed X],   Cate
goryTheory.MonoidalClosed.curry' (CategoryTheory.CategoryStruct.id X) = Category
Theory.MonoidalClosed.id X
参数：X : C；CategoryTheory.CategoryStruct.id X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma curry'_id (X : C) [Closed X] : curry' (𝟙 X) = id X := by
  dsimp [curry']
  rw [Category.comp_id]
  rfl

@[reassoc]
/-
**CategoryTheory.MonoidalClosed.whiskerLeft_curry'_ihom_ev_app** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MonoidalClosed`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C] {X Y : C}   [inst_2 : CategoryTheory.Closed X] (f : 
X ⟶ Y),   CategoryTheory.CategoryStruct.comp       (CategoryTheory.MonoidalCateg
oryStruct.whiskerLeft X (CategoryTheory.MonoidalClosed.curry' f))       ((Catego
ryTheory.ihom.ev X).app Y) =     CategoryTheory.CategoryStruct.comp (CategoryThe
ory.MonoidalCategoryStruct.rightUnitor X).hom f
参数：f : X ⟶ Y；CategoryTheory.MonoidalCategoryStruct.whiskerLeft X (CategoryTheory
.MonoidalClosed.curry' f)；(CategoryTheory.ihom.ev X).app Y；CategoryTheory.Monoid
alCategoryStruct.rightUnitor X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MonoidalClosed.whiskerLeft_curry_ihom_ev_app`：whiskerLeft
_curry_ihom_ev_app (g : A otimes Y ⟶ X) : A ◁ curry g ≫ (ihom.ev A).app X = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_curry'_ihom_ev_app {X Y : C} [Closed X] (f : X ⟶ Y) :
    X ◁ curry' f ≫ (ihom.ev X).app Y = (ρ_ _).hom ≫ f := by
  dsimp [curry']
  simp only [whiskerLeft_curry_ihom_ev_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.MonoidalClosed.curry'_whiskerRight_comp** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.MonoidalClosed`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C] {X Y Z : C}   [inst_2 : CategoryTheory.Closed X] [in
st_3 : CategoryTheory.Closed Y] (f : X ⟶ Y),   CategoryTheory.CategoryStruct.com
p       (CategoryTheory.MonoidalCategoryStruct.whiskerRight (CategoryTheory.Mono
idalClosed.curry' f) (Y ⟹ Z))       (CategoryTheory.MonoidalClosed.comp X Y Z) =
     CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.l
eftUnitor (Y ⟹ Z)).hom       ((CategoryTheory.MonoidalClosed.pre f).app Z)
参数：f : X ⟶ Y；CategoryTheory.MonoidalCategoryStruct.whiskerRight (CategoryTheory.
MonoidalClosed.curry' f) (Y ⟹ Z)；CategoryTheory.MonoidalClosed.comp X Y Z；Catego
ryTheory.MonoidalCategoryStruct.leftUnitor (Y ⟹ Z)；(CategoryTheory.MonoidalClose
d.pre f).app Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_injective`：uncurry_injective : Fun
ction.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X))
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_pre`：uncurry_pre (f : B ⟶ A) (X : 
C) : MonoidalClosed.uncurry ((pre f).app X) = f ▷ _ ≫ (ihom.ev A).app X
· 使用引理 `CategoryTheory.MonoidalClosed.comp_eq`：comp_eq (x y z : C) [Closed x] [C
losed y] : comp x y z = curry (compTranspose x y z)
· 使用定理 `CategoryTheory.MonoidalClosed.curry_natural_left`：curry_natural_left (f 
: X ⟶ X') (g : A otimes X' ⟶ Y) : curry (_ ◁ f ≫ g) = f ≫ curry g
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
· 使用引理 `CategoryTheory.MonoidalClosed.compTranspose_eq`：compTranspose_eq (x y z 
: C) [Closed x] [Closed y] : compTranspose x y z = (α_ _ _ _).inv ≫ (ihom.ev x).
app y ▷ _ ≫ (ihom.ev y).app z
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_middle_assoc`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheor
y.MonoidalCategory C] (X : C) {Y Y' : C}   (f : Y ⟶ Y') (Z :…
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
· 使用定理 `CategoryTheory.MonoidalClosed.whiskerLeft_curry'_ihom_ev_app`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoidal
Category C] {X Y : C}   [inst_2 : CategoryTheory.C…
· 使用定理 `CategoryTheory.MonoidalCategory.triangle_assoc_comp_right_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoi
dalCategory C] (X Y : C) {Z : C}   (h : CategoryTheor…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_inv_hom_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] (X : C) {Y Z : C}   (f : Y ≅ Z) {Z_1 :…
-/
lemma curry'_whiskerRight_comp {X Y Z : C} [Closed X] [Closed Y] (f : X ⟶ Y) :
    curry' f ▷ _ ≫ comp X Y Z = (λ_ _).hom ≫ (pre f).app Z := by
  rw [← cancel_epi (λ_ _).inv, Iso.inv_hom_id_assoc]
  apply uncurry_injective
  rw [uncurry_pre, comp_eq, ← curry_natural_left, ← curry_natural_left, uncurry_curry,
    compTranspose_eq, associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    whiskerLeft_curry'_ihom_ev_app, comp_whiskerRight_assoc, triangle_assoc_comp_right_assoc,
    whiskerLeft_inv_hom_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.MonoidalClosed.whiskerLeft_curry'_comp** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MonoidalClosed`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C] {X Y Z : C}   [inst_2 : CategoryTheory.Closed X] [in
st_3 : CategoryTheory.Closed Y] (f : Y ⟶ Z),   CategoryTheory.CategoryStruct.com
p       (CategoryTheory.MonoidalCategoryStruct.whiskerLeft (X ⟹ Y) (CategoryTheo
ry.MonoidalClosed.curry' f))       (CategoryTheory.MonoidalClosed.comp X Y Z) = 
    CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.ri
ghtUnitor (X ⟹ Y)).hom       ((CategoryTheory.ihom X).map f)
参数：f : Y ⟶ Z；CategoryTheory.MonoidalCategoryStruct.whiskerLeft (X ⟹ Y) (Category
Theory.MonoidalClosed.curry' f)；CategoryTheory.MonoidalClosed.comp X Y Z；Categor
yTheory.MonoidalCategoryStruct.rightUnitor (X ⟹ Y)；(CategoryTheory.ihom X).map f
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_injective`：uncurry_injective : Fun
ction.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X))
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_ihom_map`：uncurry_ihom_map (g : Y 
⟶ Y') : uncurry ((ihom A).map g) = (ihom.ev A).app Y ≫ g
· 使用引理 `CategoryTheory.MonoidalClosed.comp_eq`：comp_eq (x y z : C) [Closed x] [C
losed y] : comp x y z = curry (compTranspose x y z)
· 使用定理 `CategoryTheory.MonoidalClosed.curry_natural_left`：curry_natural_left (f 
: X ⟶ X') (g : A otimes X' ⟶ Y) : curry (_ ◁ f ≫ g) = f ≫ curry g
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
· 使用引理 `CategoryTheory.MonoidalClosed.compTranspose_eq`：compTranspose_eq (x y z 
: C) [Closed x] [Closed y] : compTranspose x y z = (α_ _ _ _).inv ≫ (ihom.ev x).
app y ▷ _ ≫ (ihom.ev y).app z
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_right_assoc`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.MonoidalCategory C] (X Y : C)   {Z Z' : C} (f : Z ⟶ Z') {Z…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.MonoidalClosed.whiskerLeft_curry'_ihom_ev_app`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoidal
Category C] {X Y : C}   [inst_2 : CategoryTheory.C…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor_inv`：whiskerLeft
_rightUnitor_inv (X Y : C) : X ◁ (ρ_ Y).inv = (ρ_ (X otimes Y)).inv ≫ (α_ X Y (𝟙
_ C)).hom
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id_assoc`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategor
y C] {X Y : C}   (f : X ⟶ Y) {Z : C}   (h :…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma whiskerLeft_curry'_comp {X Y Z : C} [Closed X] [Closed Y] (f : Y ⟶ Z) :
    _ ◁ curry' f ≫ comp X Y Z = (ρ_ _).hom ≫ (ihom X).map f := by
  rw [← cancel_epi (ρ_ _).inv, Iso.inv_hom_id_assoc]
  apply uncurry_injective
  rw [uncurry_ihom_map, comp_eq, ← curry_natural_left, ← curry_natural_left, uncurry_curry,
    compTranspose_eq, associator_inv_naturality_right_assoc, whisker_exchange_assoc]
  dsimp
  rw [whiskerLeft_curry'_ihom_ev_app, whiskerLeft_rightUnitor_inv,
    MonoidalCategory.whiskerRight_id_assoc, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
/-
**CategoryTheory.MonoidalClosed.curry'_ihom_map** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MonoidalClosed`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C] {X Y Z : C}   [inst_2 : CategoryTheory.Closed X] (f 
: X ⟶ Y) (g : Y ⟶ Z),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Monoi
dalClosed.curry' f) ((CategoryTheory.ihom X).map g) =     CategoryTheory.Monoida
lClosed.curry' (CategoryTheory.CategoryStruct.comp f g)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.MonoidalClosed.curry' f；(CategoryTheory.ih
om X).map g；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma curry'_ihom_map {X Y Z : C} [Closed X] (f : X ⟶ Y) (g : Y ⟶ Z) :
    curry' f ≫ (ihom X).map g = curry' (f ≫ g) := by
  simp only [curry', ← curry_natural_right, Category.assoc]
/-
**CategoryTheory.MonoidalClosed.curry'_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.MonoidalClosed`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C] {X Y Z : C}   [inst_2 : CategoryTheory.Closed X] [in
st_3 : CategoryTheory.Closed Y] (f : X ⟶ Y) (g : Y ⟶ Z),   CategoryTheory.Monoid
alClosed.curry' (CategoryTheory.CategoryStruct.comp f g) =     CategoryTheory.Ca
tegoryStruct.comp       (CategoryTheory.MonoidalCategoryStruct.leftUnitor (Categ
oryTheory.MonoidalCategoryStruct.tensorUnit C)).inv       (CategoryTheory.Catego
ryStruct.comp         (CategoryTheory.MonoidalCategoryStruct.tensorHom (Category
Theory.MonoidalClosed.curry' f)           (CategoryTheory.MonoidalClosed.curry' 
g))         (CategoryTheory.MonoidalClosed.comp X Y Z))
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；CategoryTheory.Mon
oidalCategoryStruct.leftUnitor (CategoryTheory.MonoidalCategoryStruct.tensorUnit
 C)；CategoryTheory.CategoryStruct.comp         (CategoryTheory.MonoidalCategoryS
truct.tensorHom (CategoryTheory.MonoidalClosed.curry' f)           (CategoryTheo
ry.MonoidalClosed.curry' g))         (CategoryTheory.MonoidalClosed.comp X Y Z)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def_assoc`：∀ {C : Type u} {𝒞 :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X
₁ Y₁ X₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalClosed.whiskerLeft_curry'_comp`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategor
y C] {X Y Z : C}   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.unitors_equal`：unitors_equal : (fun_ (𝟙_
 C)).hom = (ρ_ (𝟙_ C)).hom
· 使用定理 `CategoryTheory.MonoidalClosed.curry'_ihom_map`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] {X 
Y Z : C}   [inst_2 : CategoryTheory…
-/
lemma curry'_comp {X Y Z : C} [Closed X] [Closed Y] (f : X ⟶ Y) (g : Y ⟶ Z) :
    curry' (f ≫ g) = (λ_ (𝟙_ C)).inv ≫ (curry' f ⊗ₘ curry' g) ≫ comp X Y Z := by
  rw [tensorHom_def_assoc, whiskerLeft_curry'_comp, MonoidalCategory.whiskerRight_id,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← unitors_equal,
    Iso.inv_hom_id_assoc, curry'_ihom_map]

end OrdinaryEnriched

end MonoidalClosed

end CategoryTheory

