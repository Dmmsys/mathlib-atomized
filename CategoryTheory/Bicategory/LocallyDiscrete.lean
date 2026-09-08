/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# Locally discrete bicategories

A category `C` can be promoted to a strict bicategory `LocallyDiscrete C`. The objects and the
1-morphisms in `LocallyDiscrete C` are the same as the objects and the morphisms, respectively,
in `C`, and the 2-morphisms in `LocallyDiscrete C` are the equalities between 1-morphisms. In
other words, the category consisting of the 1-morphisms between each pair of objects `X` and `Y`
in `LocallyDiscrete C` is defined as the discrete category associated with the type `X ⟶ Y`.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory Discrete

universe w₂ w₁ v₂ v₁ v u₂ u₁ u

section

variable {C : Type u}

/-- A wrapper for promoting any category to a bicategory,
with the only 2-morphisms being equalities.
-/
@[ext]
/-
**CategoryTheory.LocallyDiscrete** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A wrapper for promoting any category to a bicategory,
with the only 2-morphisms being equalities.
-/
structure LocallyDiscrete (C : Type u) where
  /-- A wrapper for promoting any category to a bicategory,
  with the only 2-morphisms being equalities.
  -/
  as : C

namespace LocallyDiscrete

@[simp]
/-
**CategoryTheory.LocallyDiscrete.mk_as** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.LocallyDiscrete`。
形式化陈述：mk_as (a : LocallyDiscrete C) : mk a.as = a
参数：a : LocallyDiscrete C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_as (a : LocallyDiscrete C) : mk a.as = a := rfl

/-- `LocallyDiscrete C` is equivalent to the original type `C`. -/
@[simps]
/-
**CategoryTheory.LocallyDiscrete.locallyDiscreteEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.LocallyDiscrete`。
形式化陈述：locallyDiscreteEquiv : LocallyDiscrete C ≃ C where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyDiscrete C` is equivalent to the original type `C`.
-/
def locallyDiscreteEquiv : LocallyDiscrete C ≃ C where
  toFun := LocallyDiscrete.as
  invFun := LocallyDiscrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch
/-
**CategoryTheory.LocallyDiscrete.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Loca
llyDiscrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq C] : DecidableEq (LocallyDiscrete C) :=
  locallyDiscreteEquiv.decidableEq
/-
**CategoryTheory.LocallyDiscrete.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Loca
llyDiscrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited C] : Inhabited (LocallyDiscrete C) :=
  ⟨⟨default⟩⟩
/-
**CategoryTheory.LocallyDiscrete.categoryStruct** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.LocallyDiscrete`。
形式化陈述：categoryStruct [CategoryStruct.{v} C] : CategoryStruct (LocallyDiscrete C)
 where Hom a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance categoryStruct [CategoryStruct.{v} C] : CategoryStruct (LocallyDiscrete C) where
  Hom a b := Discrete (a.as ⟶ b.as)
  id a := ⟨𝟙 a.as⟩
  comp f g := ⟨f.as ≫ g.as⟩

variable [CategoryStruct.{v} C]

@[simp]
/-
**CategoryTheory.LocallyDiscrete.id_as** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.LocallyDiscrete`。
形式化陈述：id_as (a : LocallyDiscrete C) : (𝟙 a : Discrete (a.as ⟶ a.as)).as = 𝟙 a.as
参数：a : LocallyDiscrete C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_as (a : LocallyDiscrete C) : (𝟙 a : Discrete (a.as ⟶ a.as)).as = 𝟙 a.as :=
  rfl

@[simp]
/-
**CategoryTheory.LocallyDiscrete.comp_as** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.LocallyDiscrete`。
形式化陈述：comp_as {a b c : LocallyDiscrete C} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).as =
 f.as ≫ g.as
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_as {a b c : LocallyDiscrete C} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).as = f.as ≫ g.as :=
  rfl
/-
**CategoryTheory.LocallyDiscrete.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Loca
llyDiscrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) homSmallCategory (a b : LocallyDiscrete C) : SmallCategory (a ⟶ b) :=
  CategoryTheory.discreteCategory (a.as ⟶ b.as)

/-- This instance is used to see through the synonym `a ⟶ b = Discrete (a.as ⟶ b.as)`. -/
/-
**CategoryTheory.LocallyDiscrete.subsingleton2Hom** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.LocallyDiscrete`。
形式化陈述：subsingleton2Hom {a b : LocallyDiscrete C} (f g : a ⟶ b) : Subsingleton (f
 ⟶ g)
参数：f g : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance is used to see through the synonym `a ⟶ b = Discrete (a.as ⟶ b.as)
`.
-/
instance subsingleton2Hom {a b : LocallyDiscrete C} (f g : a ⟶ b) : Subsingleton (f ⟶ g) :=
  instSubsingletonDiscreteHom f g

/-- Extract the equation from a 2-morphism in a locally discrete 2-category. -/
/-
**CategoryTheory.LocallyDiscrete.eq_of_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.LocallyDiscrete`。
形式化陈述：eq_of_hom {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g
参数：η : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Discrete.ext`：∀ {α : Type u₁} {x y : CategoryTheory.Discr
ete α}, x.as = y.as → x = y

--- 原说明 ---
Extract the equation from a 2-morphism in a locally discrete 2-category.
-/
theorem eq_of_hom {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g :=
  Discrete.ext η.1.1

end LocallyDiscrete

variable (C)
variable [Category.{v} C]

/-- The locally discrete bicategory on a category is a bicategory in which the objects and the
1-morphisms are the same as those in the underlying category, and the 2-morphisms are the
equalities between 1-morphisms.
-/
/-
**CategoryTheory.locallyDiscreteBicategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory`。
形式化陈述：locallyDiscreteBicategory : Bicategory (LocallyDiscrete C) where whiskerLe
ft _ _ _ η
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The locally discrete bicategory on a category is a bicategory in which the objec
ts and the
1-morphisms are the same as those in the underlying category, and the 2-morphism
s are the
equalities between 1-morphisms.
-/
instance locallyDiscreteBicategory : Bicategory (LocallyDiscrete C) where
  whiskerLeft _ _ _ η := eqToHom (congr_arg₂ (· ≫ ·) rfl (LocallyDiscrete.eq_of_hom η))
  whiskerRight η _ := eqToHom (congr_arg₂ (· ≫ ·) (LocallyDiscrete.eq_of_hom η) rfl)
  associator f g h := eqToIso <| by apply Discrete.ext; simp
  leftUnitor f := eqToIso <| by apply Discrete.ext; simp
  rightUnitor f := eqToIso <| by apply Discrete.ext; simp

/-- A locally discrete bicategory is strict. -/
/-
**CategoryTheory.locallyDiscreteBicategory.strict** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.locallyDiscreteBicategory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C],   CategoryTheory
.Bicategory.Strict (CategoryTheory.LocallyDiscrete C)
参数：C : Type u；CategoryTheory.LocallyDiscrete C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Discrete.ext`：∀ {α : Type u₁} {x y : CategoryTheory.Discr
ete α}, x.as = y.as → x = y
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
A locally discrete bicategory is strict.
-/
instance locallyDiscreteBicategory.strict : Strict (LocallyDiscrete C) where
  id_comp _ := Discrete.ext (Category.id_comp _)
  comp_id _ := Discrete.ext (Category.comp_id _)
  assoc _ _ _ := Discrete.ext (Category.assoc _ _ _)

end

namespace Bicategory

/-- A bicategory is locally discrete if the categories of 1-morphisms are discrete. -/
/-
**CategoryTheory.Bicategory.IsLocallyDiscrete** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Bicategory`。
形式化陈述：IsLocallyDiscrete (B : Type*) [Bicategory B]
参数：B : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bicategory is locally discrete if the categories of 1-morphisms are discrete.
-/
abbrev IsLocallyDiscrete (B : Type*) [Bicategory B] := ∀ (b c : B), IsDiscrete (b ⟶ c)
/-
**CategoryTheory.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (C : Type*) [Category* C] : IsLocallyDiscrete (LocallyDiscrete C) :=
  fun _ _ ↦ Discrete.isDiscrete _
/-
**CategoryTheory.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (B : Type*) [Bicategory B] [IsLocallyDiscrete B] : Strict B where
  id_comp f := obj_ext_of_isDiscrete (leftUnitor f).hom
  comp_id f := obj_ext_of_isDiscrete (rightUnitor f).hom
  assoc f g h := obj_ext_of_isDiscrete (associator f g h).hom

end Bicategory

end CategoryTheory

section

open CategoryTheory LocallyDiscrete

universe v u

namespace Quiver.Hom

variable {C : Type u} [CategoryStruct.{v} C]

/-- The 1-morphism in `LocallyDiscrete C` associated to a given morphism `f : a ⟶ b` in `C` -/
@[simps]
/-
**Quiver.Hom.toLoc** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Hom`。
形式化陈述：toLoc {a b : C} (f : a ⟶ b) : LocallyDiscrete.mk a ⟶ LocallyDiscrete.mk b
参数：f : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 1-morphism in `LocallyDiscrete C` associated to a given morphism `f : a ⟶ b`
 in `C`
-/
def toLoc {a b : C} (f : a ⟶ b) : LocallyDiscrete.mk a ⟶ LocallyDiscrete.mk b :=
  ⟨f⟩

@[simp]
/-
**Quiver.Hom.id_toLoc** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Hom`。
形式化陈述：id_toLoc (a : C) : (𝟙 a).toLoc = 𝟙 (LocallyDiscrete.mk a)
参数：a : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_toLoc (a : C) : (𝟙 a).toLoc = 𝟙 (LocallyDiscrete.mk a) :=
  rfl

@[simp, grind _=_]
/-
**Quiver.Hom.comp_toLoc** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Hom`。
形式化陈述：comp_toLoc {a b c : C} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).toLoc = f.toLoc ≫
 g.toLoc
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_toLoc {a b c : C} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).toLoc = f.toLoc ≫ g.toLoc :=
  rfl

end Quiver.Hom

@[simp]
/-
**CategoryTheory.LocallyDiscrete.eqToHom_toLoc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CategoryTheory.LocallyDiscrete.eqToHom_toLoc {C : Type u} [Category.{v} C]
 {a b : C} (h : a = b) : (eqToHom h).toLoc = eqToHom (congrArg LocallyDiscrete.m
k h)
参数：h : a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma CategoryTheory.LocallyDiscrete.eqToHom_toLoc {C : Type u} [Category.{v} C] {a b : C}
    (h : a = b) : (eqToHom h).toLoc = eqToHom (congrArg LocallyDiscrete.mk h) := by
  subst h; rfl
/-
**CategoryTheory.CommSq.toLoc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CategoryTheory.CommSq.toLoc {C : Type*} [Category C] {X₁ X₂ X₃ X₄ : C} {t 
: X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (h : CommSq t l r b) : Comm
Sq t.toLoc l.toLoc r.toLoc b.toLoc
参数：h : CommSq t l r b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallyDiscreteBicategory.strict`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C],   CategoryTheory.Bicategory.Strict (CategoryT
heory.LocallyDiscrete C)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma CategoryTheory.CommSq.toLoc {C : Type*} [Category C] {X₁ X₂ X₃ X₄ : C}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (h : CommSq t l r b) :
    CommSq t.toLoc l.toLoc r.toLoc b.toLoc :=
  ⟨by simp only [← Quiver.Hom.comp_toLoc, h.w]⟩

end

