/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Comonoid objects in a Cartesian monoidal category.

The category of comonoid objects in a Cartesian monoidal category is equivalent
to the category itself, via the forgetful functor.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits ComonObj

universe v u

noncomputable section

namespace CategoryTheory
variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local simp] leftUnitor_hom rightUnitor_hom

/--
The functor from a Cartesian monoidal category to comonoids in that category,
equipping every object with the diagonal map as a comultiplication.
-/
/-
**CategoryTheory.cartesianComon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：cartesianComon : C ⥤ Comon C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from a Cartesian monoidal category to comonoids in that category,
equipping every object with the diagonal map as a comultiplication.
-/
def cartesianComon : C ⥤ Comon C where
  obj X := {
    X := X
    comon := {
      comul := lift (𝟙 _) (𝟙 _)
      counit := toUnit _
    }
  }
  map f := .mk' f (f_comul := by
    #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
    this argument was provided by the auto_param. -/
    simp +instances)

variable {C}
/-
**CategoryTheory.counit_eq_toUnit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C] (A : C)   [inst_2 : CategoryTheory.ComonObj
 A],   CategoryTheory.ComonObj.counit = CategoryTheory.SemiCartesianMonoidalCate
gory.toUnit A
参数：A : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
-/
@[simp] theorem counit_eq_toUnit (A : C) [ComonObj A] : ε[A] = toUnit _ := by ext
/-
**CategoryTheory.comul_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C] (A : C)   [inst_2 : CategoryTheory.ComonObj
 A],   CategoryTheory.ComonObj.comul =     CategoryTheory.CartesianMonoidalCateg
ory.lift (CategoryTheory.CategoryStruct.id A)       (CategoryTheory.CategoryStru
ct.id A)
参数：A : C；CategoryTheory.CategoryStruct.id A；CategoryTheory.CategoryStruct.id A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.counit_eq_toUnit`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C] (A : C) 
  [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_fst`：whiskerLeft_fs
t (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.rightUnitor_inv_fst`：rightUnito
r_inv_fst (X : C) : (ρ_ X).inv ≫ fst _ _ = 𝟙 X
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.ComonObj.comul_counit`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)  
 [self : CategoryTheory.Co…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_snd`：whiskerRight_
snd {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ snd _ _ = snd _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.leftUnitor_inv_snd`：leftUnitor_
inv_snd (X : C) : (fun_ X).inv ≫ snd _ _ = 𝟙 X
· 使用定理 `CategoryTheory.ComonObj.counit_comul`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)  
 [self : CategoryTheory.Co…
-/
@[simp] theorem comul_eq_lift (A : C) [ComonObj A] : Δ[A] = lift (𝟙 _) (𝟙 _) := by
  ext
  · simpa using comul_counit A =≫ fst _ _
  · simpa using counit_comul A =≫ snd _ _

set_option backward.isDefEq.respectTransparency false in
/--
Every comonoid object in a Cartesian monoidal category is equivalent to
the canonical comonoid structure on the underlying object.
-/
/-
**CategoryTheory.isoCartesianComon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] →       (A : CategoryTheory.Comon C
) → A ≅ (CategoryTheory.cartesianComon C).obj A.X
参数：A : CategoryTheory.Comon C；CategoryTheory.cartesianComon C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every comonoid object in a Cartesian monoidal category is equivalent to
the canonical comonoid structure on the underlying object.
-/
@[simps] def isoCartesianComon (A : Comon C) : A ≅ (cartesianComon C).obj A.X :=
  { hom := .mk' (𝟙 _)
    inv := .mk' (𝟙 _) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The category of comonoid objects in a Cartesian monoidal category is equivalent
to the category itself, via the forgetful functor.
-/
/-
**CategoryTheory.comonEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] → CategoryTheory.Comon C ≌ C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of comonoid objects in a Cartesian monoidal category is equivalent
to the category itself, via the forgetful functor.
-/
@[simps] def comonEquiv : Comon C ≌ C where
  functor := Comon.forget C
  inverse := cartesianComon C
  unitIso := NatIso.ofComponents isoCartesianComon
  counitIso := NatIso.ofComponents (fun _ => .refl _)

end CategoryTheory

