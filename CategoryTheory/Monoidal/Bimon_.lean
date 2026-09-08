/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# The category of bimonoids in a braided monoidal category.

We define bimonoids in a braided monoidal category `C`
as comonoid objects in the category of monoid objects in `C`.

We verify that this is equivalent to the monoid objects in the category of comonoid objects.

## TODO
* Construct the category of modules, and show that it is monoidal with a monoidal forgetful functor
  to `C`.
* Some form of Tannaka reconstruction:
  given a monoidal functor `F : C ⥤ D` into a braided category `D`,
  the internal endomorphisms of `F` form a bimonoid in presheaves on `D`,
  in good circumstances this is representable by a bimonoid in `D`, and then
  `C` is monoidally equivalent to the modules over that bimonoid.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

open scoped MonObj ComonObj

/--
A bimonoid object in a braided category `C` is an object that is simultaneously monoid and comonoid
objects, and structure morphisms of them satisfy appropriate consistency conditions.
-/
/-
**CategoryTheory.BimonObj** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：BimonObj (M : C) extends MonObj M, ComonObj M where mul_comul (M) : μ[M] ≫
 Δ[M] = (Δ[M] otimesₘ Δ[M]) ≫ tensorμ M M M M ≫ (μ[M] otimesₘ μ[M])
参数：M : C；M。
继承自：MonObj M, ComonObj M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bimonoid object in a braided category `C` is an object that is simultaneously 
monoid and comonoid
objects, and structure morphisms of them satisfy appropriate consistency conditi
ons.
-/
class BimonObj (M : C) extends MonObj M, ComonObj M where
  mul_comul (M) : μ[M] ≫ Δ[M] = (Δ[M] ⊗ₘ Δ[M]) ≫ tensorμ M M M M ≫ (μ[M] ⊗ₘ μ[M]) := by cat_disch
  one_comul (M) : η[M] ≫ Δ[M] = η[M ⊗ M] := by cat_disch
  mul_counit (M) : μ[M] ≫ ε[M] = ε[M ⊗ M] := by cat_disch
  one_counit (M) : η[M] ≫ ε[M] = 𝟙 (𝟙_ C) := by cat_disch

namespace BimonObj

attribute [reassoc (attr := simp)] mul_comul one_comul mul_counit one_counit

end BimonObj

/-- The property that a morphism between bimonoid objects is a bimonoid morphism. -/
/-
**CategoryTheory.IsBimonHom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       [inst_2 : CategoryTheory.BraidedC
ategory C] →         {M N : C} → [CategoryTheory.BimonObj M] → [CategoryTheory.B
imonObj N] → (M ⟶ N) → Prop
参数：M ⟶ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a morphism between bimonoid objects is a bimonoid morphism.
-/
class IsBimonHom {M N : C} [BimonObj M] [BimonObj N] (f : M ⟶ N) : Prop extends
    IsMonHom f, IsComonHom f

variable (C) in
/--
A bimonoid object in a braided category `C` is a comonoid object in the (monoidal)
category of monoid objects in `C`.
-/
/-
**CategoryTheory.Bimon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Bimon
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bimonoid object in a braided category `C` is a comonoid object in the (monoida
l)
category of monoid objects in `C`.
-/
def Bimon := Comon (Mon C)

namespace Bimon

/-
**CategoryTheory.Bimon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bimon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Bimon C) := inferInstanceAs (Category (Comon (Mon C)))
/-
**CategoryTheory.Bimon.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Bimon`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] {X 
Y : CategoryTheory.Bimon C} {f g : X ⟶ Y},   f.hom.hom = g.hom.hom → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comon.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cat
egory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {M N : Category
Theory.Comon C} {x…
· 使用定理 `CategoryTheory.Mon.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Categ
ory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {M N : CategoryTh
eory.Mon C} {x y…
-/
@[ext] lemma ext {X Y : Bimon C} {f g : X ⟶ Y} (w : f.hom.hom = g.hom.hom) : f = g :=
  Comon.Hom.ext (Mon.Hom.ext w)
/-
**CategoryTheory.Bimon.id_hom'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Bimon`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] (M 
: CategoryTheory.Bimon C),   (CategoryTheory.CategoryStruct.id M).hom = Category
Theory.CategoryStruct.id M.X
参数：M : CategoryTheory.Bimon C；CategoryTheory.CategoryStruct.id M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem id_hom' (M : Bimon C) : Comon.Hom.hom (𝟙 M) = 𝟙 M.X := rfl

@[simp]
/-
**CategoryTheory.Bimon.comp_hom'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Bimon
`。
形式化陈述：comp_hom' {M N K : Bimon C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom 
≫ g.hom
参数：f : M ⟶ N；g : N ⟶ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_hom' {M N K : Bimon C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (C)

/-- The forgetful functor from bimonoid objects to monoid objects. -/
/-
**CategoryTheory.Bimon.toMon** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Bimon`。
形式化陈述：toMon : Bimon C ⥤ Mon C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from bimonoid objects to monoid objects.
-/
abbrev toMon : Bimon C ⥤ Mon C := Comon.forget (Mon C)

/-- The forgetful functor from bimonoid objects to the underlying category. -/
/-
**CategoryTheory.Bimon.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bimon`。
形式化陈述：forget : Bimon C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from bimonoid objects to the underlying category.
-/
def forget : Bimon C ⥤ C := toMon C ⋙ Mon.forget C

@[simp]
/-
**CategoryTheory.Bimon.toMon_forget** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Bi
mon`。
形式化陈述：toMon_forget : toMon C ⋙ Mon.forget C = forget C
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMon_forget : toMon C ⋙ Mon.forget C = forget C := rfl

/-- The forgetful functor from bimonoid objects to comonoid objects. -/
@[simps!]
/-
**CategoryTheory.Bimon.toComon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bimon`。
形式化陈述：toComon : Bimon C ⥤ Comon C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from bimonoid objects to comonoid objects.
-/
def toComon : Bimon C ⥤ Comon C := (Mon.forget C).mapComon

@[simp]
/-
**CategoryTheory.Bimon.toComon_forget** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Bimon`。
形式化陈述：toComon_forget : toComon C ⋙ Comon.forget C = forget C
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toComon_forget : toComon C ⋙ Comon.forget C = forget C := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- The object level part of the forward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
/-
**CategoryTheory.Bimon.toMonComonObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.B
imon`。
形式化陈述：toMonComonObj (M : Bimon C) : Mon (Comon C) where X
参数：M : Bimon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object level part of the forward direction of `Comon (Mon C) ≌ Mon (Comon C)
`
-/
def toMonComonObj (M : Bimon C) : Mon (Comon C) where
  X := (toComon C).obj M
  mon.one := .mk' η[M.X.X]
  mon.mul.hom := μ[M.X.X]
  mon.mul.isComonHom_hom.hom_comul := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The forward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
/-
**CategoryTheory.Bimon.toMonComon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bimo
n`。
形式化陈述：toMonComon : Bimon C ⥤ Mon (Comon C) where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forward direction of `Comon (Mon C) ≌ Mon (Comon C)`
-/
def toMonComon : Bimon C ⥤ Mon (Comon C) where
  obj := toMonComonObj
  map f := .mk' ((toComon C).map f)

variable {C}

/-- Auxiliary definition for `ofMonComonObj`. -/
@[simps! X]
/-
**CategoryTheory.Bimon.ofMonComonObjX** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Bimon`。
形式化陈述：ofMonComonObjX (M : Mon (Comon C)) : Mon C
参数：M : Mon (Comon C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `ofMonComonObj`.
-/
def ofMonComonObjX (M : Mon (Comon C)) : Mon C := (Comon.forget C).mapMon.obj M

@[simp]
/-
**CategoryTheory.Bimon.ofMonComonObjX_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Bimon`。
形式化陈述：ofMonComonObjX_one (M : Mon (Comon C)) : η[(ofMonComonObjX M).X] = 𝟙 (𝟙_ C
) ≫ η[M.X].hom
参数：M : Mon (Comon C)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMonComonObjX_one (M : Mon (Comon C)) :
    η[(ofMonComonObjX M).X] = 𝟙 (𝟙_ C) ≫ η[M.X].hom :=
  rfl

@[simp]
/-
**CategoryTheory.Bimon.ofMonComonObjX_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Bimon`。
形式化陈述：ofMonComonObjX_mul (M : Mon (Comon C)) : μ[(ofMonComonObjX M).X] = 𝟙 (M.X.
X otimes M.X.X) ≫ μ[M.X].hom
参数：M : Mon (Comon C)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMonComonObjX_mul (M : Mon (Comon C)) :
    μ[(ofMonComonObjX M).X] = 𝟙 (M.X.X ⊗ M.X.X) ≫ μ[M.X].hom :=
  rfl

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] ComonObj.instTensorUnit in
attribute [local simp] MonObj.tensorObj.one_def MonObj.tensorObj.mul_def tensorμ in
/-- The object level part of the backward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
/-
**CategoryTheory.Bimon.ofMonComonObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.B
imon`。
形式化陈述：ofMonComonObj (M : Mon (Comon C)) : Bimon C where X
参数：M : Mon (Comon C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object level part of the backward direction of `Comon (Mon C) ≌ Mon (Comon C
)`
-/
def ofMonComonObj (M : Mon (Comon C)) : Bimon C where
  X := ofMonComonObjX M
  comon.counit := .mk' ε[M.X.X]
  comon.comul := .mk' Δ[M.X.X]

set_option backward.isDefEq.respectTransparency.types false in
variable (C) in
/-- The backward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
/-
**CategoryTheory.Bimon.ofMonComon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bimo
n`。
形式化陈述：ofMonComon : Mon (Comon C) ⥤ Bimon C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The backward direction of `Comon (Mon C) ≌ Mon (Comon C)`
-/
def ofMonComon : Mon (Comon C) ⥤ Bimon C where
  obj := ofMonComonObj
  map f := .mk' ((Comon.forget C).mapMon.map f)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Bimon.toMonComon_ofMonComon_obj_one** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Bimon`。
形式化陈述：toMonComon_ofMonComon_obj_one (M : Bimon C) : η[((toMonComon C ⋙ ofMonComo
n C).obj M).X.X] = 𝟙 _ ≫ η[M.X.X]
参数：M : Bimon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMonComon_ofMonComon_obj_one (M : Bimon C) :
    η[((toMonComon C ⋙ ofMonComon C).obj M).X.X] = 𝟙 _ ≫ η[M.X.X] :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Bimon.toMonComon_ofMonComon_obj_mul** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Bimon`。
形式化陈述：toMonComon_ofMonComon_obj_mul (M : Bimon C) : μ[((toMonComon C ⋙ ofMonComo
n C).obj M).X.X] = 𝟙 _ ≫ μ[M.X.X]
参数：M : Bimon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMonComon_ofMonComon_obj_mul (M : Bimon C) :
    μ[((toMonComon C ⋙ ofMonComon C).obj M).X.X] = 𝟙 _ ≫ μ[M.X.X] :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `equivMonComonUnitIsoApp`. -/
@[simps!]
/-
**CategoryTheory.Bimon.equivMonComonUnitIsoAppXAux** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Bimon`。
形式化陈述：equivMonComonUnitIsoAppXAux (M : Bimon C) : M.X.X ≅ ((toMonComon C ⋙ ofMon
Comon C).obj M).X.X
参数：M : Bimon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `equivMonComonUnitIsoApp`.
-/
def equivMonComonUnitIsoAppXAux (M : Bimon C) :
    M.X.X ≅ ((toMonComon C ⋙ ofMonComon C).obj M).X.X :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Bimon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bimon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Bimon C) : IsMonHom (equivMonComonUnitIsoAppXAux M).hom where

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `equivMonComonUnitIsoApp`. -/
@[simps!]
/-
**CategoryTheory.Bimon.equivMonComonUnitIsoAppX** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Bimon`。
形式化陈述：equivMonComonUnitIsoAppX (M : Bimon C) : M.X ≅ ((toMonComon C ⋙ ofMonComon
 C).obj M).X
参数：M : Bimon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `equivMonComonUnitIsoApp`.
-/
def equivMonComonUnitIsoAppX (M : Bimon C) :
    M.X ≅ ((toMonComon C ⋙ ofMonComon C).obj M).X :=
  Mon.mkIso (equivMonComonUnitIsoAppXAux M)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Bimon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bimon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Bimon C) : IsComonHom (equivMonComonUnitIsoAppX M).hom where

/-- The unit for the equivalence `Comon (Mon C) ≌ Mon (Comon C)`. -/
@[simps!]
/-
**CategoryTheory.Bimon.equivMonComonUnitIsoApp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Bimon`。
形式化陈述：equivMonComonUnitIsoApp (M : Bimon C) : M ≅ (toMonComon C ⋙ ofMonComon C).
obj M
参数：M : Bimon C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bimon.instIsComonHomMonHomEquivMonComonUnitIsoAppX`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.
MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedC…

--- 原说明 ---
The unit for the equivalence `Comon (Mon C) ≌ Mon (Comon C)`.
-/
def equivMonComonUnitIsoApp (M : Bimon C) :
    M ≅ (toMonComon C ⋙ ofMonComon C).obj M :=
  Comon.mkIso' (equivMonComonUnitIsoAppX M)

@[simp]
/-
**CategoryTheory.Bimon.ofMonComon_toMonComon_obj_counit** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Bimon`。
形式化陈述：ofMonComon_toMonComon_obj_counit (M : Mon (Comon C)) : ε[((ofMonComon C ⋙ 
toMonComon C).obj M).X.X] = ε[M.X.X] ≫ 𝟙 _
参数：M : Mon (Comon C)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMonComon_toMonComon_obj_counit (M : Mon (Comon C)) :
    ε[((ofMonComon C ⋙ toMonComon C).obj M).X.X] = ε[M.X.X] ≫ 𝟙 _ :=
  rfl

@[simp]
/-
**CategoryTheory.Bimon.ofMonComon_toMonComon_obj_comul** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Bimon`。
形式化陈述：ofMonComon_toMonComon_obj_comul (M : Mon (Comon C)) : Δ[((ofMonComon C ⋙ t
oMonComon C).obj M).X.X] = Δ[M.X.X] ≫ 𝟙 _
参数：M : Mon (Comon C)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMonComon_toMonComon_obj_comul (M : Mon (Comon C)) :
    Δ[((ofMonComon C ⋙ toMonComon C).obj M).X.X] = Δ[M.X.X] ≫ 𝟙 _ :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `equivMonComonCounitIsoApp`. -/
@[simps!]
/-
**CategoryTheory.Bimon.equivMonComonCounitIsoAppXAux** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Bimon`。
形式化陈述：equivMonComonCounitIsoAppXAux (M : Mon (Comon C)) : ((ofMonComon C ⋙ toMon
Comon C).obj M).X.X ≅ M.X.X
参数：M : Mon (Comon C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `equivMonComonCounitIsoApp`.
-/
def equivMonComonCounitIsoAppXAux (M : Mon (Comon C)) :
    ((ofMonComon C ⋙ toMonComon C).obj M).X.X ≅ M.X.X :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Bimon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bimon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Mon (Comon C)) : IsComonHom (equivMonComonCounitIsoAppXAux M).hom where

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `equivMonComonCounitIsoApp`. -/
@[simps!]
/-
**CategoryTheory.Bimon.equivMonComonCounitIsoAppX** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Bimon`。
形式化陈述：equivMonComonCounitIsoAppX (M : Mon (Comon C)) : ((ofMonComon C ⋙ toMonCom
on C).obj M).X ≅ M.X
参数：M : Mon (Comon C)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bimon.instIsComonHomHomEquivMonComonCounitIsoAppXAux`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheor
y.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedC…

--- 原说明 ---
Auxiliary definition for `equivMonComonCounitIsoApp`.
-/
def equivMonComonCounitIsoAppX (M : Mon (Comon C)) :
    ((ofMonComon C ⋙ toMonComon C).obj M).X ≅ M.X :=
  Comon.mkIso' (equivMonComonCounitIsoAppXAux M)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Bimon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bimon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Mon (Comon C)) : IsMonHom (equivMonComonCounitIsoAppX M).hom where

set_option backward.isDefEq.respectTransparency false in
/-- The counit for the equivalence `Comon (Mon C) ≌ Mon (Comon C)`. -/
@[simps!]
/-
**CategoryTheory.Bimon.equivMonComonCounitIsoApp** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Bimon`。
形式化陈述：equivMonComonCounitIsoApp (M : Mon (Comon C)) : (ofMonComon C ⋙ toMonComon
 C).obj M ≅ M
参数：M : Mon (Comon C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit for the equivalence `Comon (Mon C) ≌ Mon (Comon C)`.
-/
def equivMonComonCounitIsoApp (M : Mon (Comon C)) :
    (ofMonComon C ⋙ toMonComon C).obj M ≅ M :=
  Mon.mkIso <| (equivMonComonCounitIsoAppX M)

set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence `Comon (Mon C) ≌ Mon (Comon C)` -/
/-
**CategoryTheory.Bimon.equivMonComon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.B
imon`。
形式化陈述：equivMonComon : Bimon C ≌ Mon (Comon C) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `Comon (Mon C) ≌ Mon (Comon C)`
-/
def equivMonComon : Bimon C ≌ Mon (Comon C) where
  functor := toMonComon C
  inverse := ofMonComon C
  unitIso := NatIso.ofComponents equivMonComonUnitIsoApp
  counitIso := NatIso.ofComponents equivMonComonCounitIsoApp

/-! ### The trivial bimonoid -/

variable (C) in
/-- The trivial bimonoid object. -/
@[simps!]
/-
**CategoryTheory.Bimon.trivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bimon`。
形式化陈述：trivial : Bimon C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial bimonoid object.
-/
def trivial : Bimon C := Comon.trivial (Mon C)

set_option backward.isDefEq.respectTransparency.types false in
/-- The bimonoid morphism from the trivial bimonoid to any bimonoid. -/
@[simps]
/-
**CategoryTheory.Bimon.trivialTo** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bimon
`。
形式化陈述：trivialTo (A : Bimon C) : trivial C ⟶ A
参数：A : Bimon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bimonoid morphism from the trivial bimonoid to any bimonoid.
-/
def trivialTo (A : Bimon C) : trivial C ⟶ A :=
  .mk' (default : Mon.trivial C ⟶ A.X)

set_option backward.isDefEq.respectTransparency.types false in
/-- The bimonoid morphism from any bimonoid to the trivial bimonoid. -/
@[simps!]
/-
**CategoryTheory.Bimon.toTrivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bimon
`。
形式化陈述：toTrivial (A : Bimon C) : A ⟶ trivial C
参数：A : Bimon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bimonoid morphism from any bimonoid to the trivial bimonoid.
-/
def toTrivial (A : Bimon C) : A ⟶ trivial C :=
  (default : @Quiver.Hom (Comon (Mon C)) _ A (Comon.trivial (Mon C)))

/-! ### Additional lemmas -/

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Bimon.BimonObjAux_counit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Bimon`。
形式化陈述：BimonObjAux_counit (M : Bimon C) : ε[((toComon C).obj M).X] = ε[M.X].hom
参数：M : Bimon C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
### Additional lemmas
-/
theorem BimonObjAux_counit (M : Bimon C) :
    ε[((toComon C).obj M).X] = ε[M.X].hom :=
  Category.comp_id _

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Bimon.BimonObjAux_comul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Bimon`。
形式化陈述：BimonObjAux_comul (M : Bimon C) : Δ[((toComon C).obj M).X] = Δ[M.X].hom
参数：M : Bimon C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem BimonObjAux_comul (M : Bimon C) :
    Δ[((toComon C).obj M).X] = Δ[M.X].hom :=
  Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Bimon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bimon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Bimon C) : BimonObj M.X.X where
  counit := ε[M.X].hom
  comul := Δ[M.X].hom
  counit_comul := by
    rw [← BimonObjAux_counit, ← BimonObjAux_comul, ComonObj.counit_comul]
  comul_counit := by
    rw [← BimonObjAux_counit, ← BimonObjAux_comul, ComonObj.comul_counit]
  comul_assoc := by
    simp_rw [← BimonObjAux_comul, ComonObj.comul_assoc]

attribute [local simp] MonObj.tensorObj.one_def in
@[reassoc]
/-
**CategoryTheory.Bimon.one_comul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Bimon
`。
形式化陈述：one_comul (M : C) [BimonObj M] : η[M] ≫ Δ[M] = (fun_ _).inv ≫ (η[M] otimes
ₘ η[M])
参数：M : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.BimonObj.one_comul`：∀ {C : Type u₁} {inst : CategoryTheor
y.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst_2 : 
CategoryTheory.BraidedC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_comul (M : C) [BimonObj M] :
    η[M] ≫ Δ[M] = (λ_ _).inv ≫ (η[M] ⊗ₘ η[M]) := by
  simp

@[reassoc]
/-
**CategoryTheory.Bimon.mul_counit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Bimo
n`。
形式化陈述：mul_counit (M : C) [BimonObj M] : μ[M] ≫ ε[M] = (ε[M] otimesₘ ε[M]) ≫ (fun
_ _).hom
参数：M : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.BimonObj.mul_counit`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst_2 :
 CategoryTheory.BraidedC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_counit (M : C) [BimonObj M] :
    μ[M] ≫ ε[M] = (ε[M] ⊗ₘ ε[M]) ≫ (λ_ _).hom := by
  simp

/-- Compatibility of the monoid and comonoid structures, in terms of morphisms in `C`. -/
/-
**CategoryTheory.Bimon.compatibility** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.B
imon`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] (M 
: C) [inst_3 : CategoryTheory.BimonObj M],   CategoryTheory.CategoryStruct.comp 
      (CategoryTheory.MonoidalCategoryStruct.tensorHom CategoryTheory.ComonObj.c
omul CategoryTheory.ComonObj.comul)       (CategoryTheory.CategoryStruct.comp   
      (CategoryTheory.MonoidalCategoryStruct.associator M M (CategoryTheory.Mono
idalCategoryStruct.tensorObj M M)).hom         (CategoryTheory.CategoryStruct.co
mp           (CategoryTheory.MonoidalCategoryStruct.whiskerLeft M             (C
ategoryTheory.MonoidalCategoryStruct.associator M M M).inv)           (CategoryT
heory.CategoryStruct.comp             (CategoryTheory.MonoidalCategoryStruct.whi
skerLeft M               (CategoryTheory.MonoidalCategoryStruct.whiskerRight (β_
 M M).hom M))             (CategoryTheory.CategoryStruct.comp               (Cat
egoryTheory.MonoidalCategoryStruct.whiskerLeft M                 (CategoryTheory
.MonoidalCategoryStruct.associator M M M).hom)               (CategoryTheory.Cat
egoryStruct.comp                 (CategoryTheory.MonoidalCategoryStruct.associat
or M M                     (CategoryTheory.MonoidalCategoryStruct.tensorObj M M)
).inv                 (CategoryTheory.MonoidalCategoryStruct.tensorHom CategoryT
heory.MonObj.mul                   CategoryTheory.MonObj.mul)))))) =     Categor
yTheory.CategoryStruct.comp CategoryTheory.MonObj.mul CategoryTheory.ComonObj.co
mul
参数：M : C；CategoryTheory.MonoidalCategoryStruct.tensorHom CategoryTheory.ComonObj
.comul CategoryTheory.ComonObj.comul；CategoryTheory.CategoryStruct.comp         
(CategoryTheory.MonoidalCategoryStruct.associator M M (CategoryTheory.MonoidalCa
tegoryStruct.tensorObj M M)).hom         (CategoryTheory.CategoryStruct.comp    
       (CategoryTheory.MonoidalCategoryStruct.whiskerLeft M             (Categor
yTheory.MonoidalCategoryStruct.associator M M M).inv)           (CategoryTheory.
CategoryStruct.comp             (CategoryTheory.MonoidalCategoryStruct.whiskerLe
ft M               (CategoryTheory.MonoidalCategoryStruct.whiskerRight (β_ M M).
hom M))             (CategoryTheory.CategoryStruct.comp               (CategoryT
heory.MonoidalCategoryStruct.whiskerLeft M                 (CategoryTheory.Monoi
dalCategoryStruct.associator M M M).hom)               (CategoryTheory.CategoryS
truct.comp                 (CategoryTheory.MonoidalCategoryStruct.associator M M
                     (CategoryTheory.MonoidalCategoryStruct.tensorObj M M)).inv 
                (CategoryTheory.MonoidalCategoryStruct.tensorHom CategoryTheory.
MonObj.mul                   CategoryTheory.MonObj.mul)))))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.BimonObj.mul_comul`：∀ {C : Type u₁} {inst : CategoryTheor
y.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst_2 : 
CategoryTheory.BraidedC…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Compatibility of the monoid and comonoid structures, in terms of morphisms in `C
`.
-/
@[reassoc (attr := simp)] theorem compatibility (M : C) [BimonObj M] :
    (Δ[M] ⊗ₘ Δ[M]) ≫
      (α_ _ _ (M ⊗ M)).hom ≫ M ◁ (α_ _ _ _).inv ≫
      M ◁ (β_ M M).hom ▷ M ≫
      M ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫
      (μ[M] ⊗ₘ μ[M]) =
    μ[M] ≫ Δ[M] := by
  simp only [BimonObj.mul_comul, tensorμ, Category.assoc]

/-- Auxiliary definition for `Bimon.mk'`. -/
@[simps X]
/-
**CategoryTheory.Bimon.mk'X** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bimon`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       [inst_2 : CategoryTheory.BraidedC
ategory C] → (X : C) → [CategoryTheory.BimonObj X] → CategoryTheory.Mon C
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Bimon.mk'`.
-/
def mk'X (X : C) [BimonObj X] : Mon C := { X := X }

set_option backward.isDefEq.respectTransparency false in
/-- Construct an object of `Bimon C` from an object `X : C` and `BimonObj X` instance. -/
@[simps X]
/-
**CategoryTheory.Bimon.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bimon`。
形式化陈述：mk'X (X : C) [BimonObj X] : Mon C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an object of `Bimon C` from an object `X : C` and `BimonObj X` instanc
e.
-/
def mk' (X : C) [BimonObj X] : Bimon C where
  X := mk'X X
  comon :=
    { counit := .mk' (ε : X ⟶ 𝟙_ C)
      comul := .mk' (Δ : X ⟶ X ⊗ X) }

end Bimon
end CategoryTheory

