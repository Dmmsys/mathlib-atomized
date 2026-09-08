/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# The category of commutative groups in a Cartesian monoidal category
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory Mon Grp CommMon
open MonObj

namespace CategoryTheory
variable (C : Type u₁) [Category.{v₁} C] [CartesianMonoidalCategory.{v₁} C] [BraidedCategory C]

/-- A commutative group object internal to a Cartesian monoidal category. -/
/-
**CategoryTheory.CommGrp** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] → [CategoryTheory.BraidedCategor
y C] → Type (max u₁ v₁)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative group object internal to a Cartesian monoidal category.
-/
structure CommGrp where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [grp : GrpObj X]
  [comm : IsCommMonObj X]

attribute [instance] CommGrp.grp CommGrp.comm

namespace CommGrp

variable {C}

/-- A commutative group object is a group object. -/
@[simps -isSimp X]
/-
**CategoryTheory.CommGrp.toGrp** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.CommG
rp`。
形式化陈述：toGrp (A : CommGrp C) : Grp C
参数：A : CommGrp C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative group object is a group object.
-/
abbrev toGrp (A : CommGrp C) : Grp C := ⟨A.X⟩

/-- A commutative group object is a commutative monoid object. -/
@[simps X]
/-
**CategoryTheory.CommGrp.toCommMon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Com
mGrp`。
形式化陈述：toCommMon (A : CommGrp C) : CommMon C
参数：A : CommGrp C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommGrp.comm`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   [inst_2
 : CategoryTheory…

--- 原说明 ---
A commutative group object is a commutative monoid object.
-/
def toCommMon (A : CommGrp C) : CommMon C := ⟨A.X⟩

/-- A commutative group object is a monoid object. -/
/-
**CategoryTheory.CommGrp.toMon** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.CommG
rp`。
形式化陈述：toMon (A : CommGrp C) : Mon C
参数：A : CommGrp C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative group object is a monoid object.
-/
abbrev toMon (A : CommGrp C) : Mon C := (toCommMon A).toMon

variable (C) in
/-- The trivial commutative group object. -/
@[simps!]
/-
**CategoryTheory.CommGrp.trivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommG
rp`。
形式化陈述：trivial : CommGrp C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial commutative group object.
-/
def trivial : CommGrp C := { X := 𝟙_ C }
/-
**CategoryTheory.CommGrp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (CommGrp C) where
  default := trivial C
/-
**CategoryTheory.CommGrp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (CommGrp C) :=
  inferInstanceAs (Category (InducedCategory _ CommGrp.toGrp))

@[simp]
/-
**CategoryTheory.CommGrp.id_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CommGr
p`。
形式化陈述：id_hom (A : CommGrp C) : (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.toGrp
参数：A : CommGrp C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_hom (A : CommGrp C) : (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.toGrp :=
  rfl

@[simp]
/-
**CategoryTheory.CommGrp.comp_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comm
Grp`。
形式化陈述：comp_hom {R S T : CommGrp C} (f : R ⟶ S) (g : S ⟶ T) : (f ≫ g).hom = f.hom
 ≫ g.hom
参数：f : R ⟶ S；g : S ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_hom {R S T : CommGrp C} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[ext]
/-
**CategoryTheory.CommGrp.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CommG
rp`。
形式化陈述：hom_ext {A B : CommGrp C} (f g : A ⟶ B) (h : f.hom.hom.hom = g.hom.hom.hom
) : f = g
参数：f g : A ⟶ B；h : f.hom.hom.hom = g.hom.hom.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.Grp.hom_ext`：hom_ext {A B : Grp C} (f g : A ⟶ B) (h : f.h
om.hom = g.hom.hom) : f = g
-/
theorem hom_ext {A B : CommGrp C} (f g : A ⟶ B) (h : f.hom.hom.hom = g.hom.hom.hom) : f = g :=
  InducedCategory.hom_ext (Grp.hom_ext _ _ h)

section

variable (C)

/-- The forgetful functor from commutative group objects to group objects. -/
@[simps! obj_X]
/-
**CategoryTheory.CommGrp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommGr
p`。
形式化陈述：forget : CommGrp C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from commutative group objects to group objects.
-/
def forget₂Grp : CommGrp C ⥤ Grp C :=
  inducedFunctor CommGrp.toGrp

/-- The forgetful functor from commutative group objects to group objects is fully faithful. -/
/-
**CategoryTheory.CommGrp.fullyFaithfulForget** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.CommGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from commutative group objects to group objects is fully f
aithful.
-/
def fullyFaithfulForget₂Grp : (forget₂Grp C).FullyFaithful :=
  fullyFaithfulInducedFunctor _
/-
**CategoryTheory.CommGrp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂Grp C).Full := InducedCategory.full _
/-
**CategoryTheory.CommGrp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂Grp C).Faithful := InducedCategory.faithful _

@[simp]
/-
**CategoryTheory.CommGrp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommGr
p`。
形式化陈述：forget : CommGrp C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂Grp_obj_one (A : CommGrp C) : η[((forget₂Grp C).obj A).X] = η[A.X] :=
  rfl

@[simp]
/-
**CategoryTheory.CommGrp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommGr
p`。
形式化陈述：forget : CommGrp C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂Grp_obj_mul (A : CommGrp C) : μ[((forget₂Grp C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
/-
**CategoryTheory.CommGrp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommGr
p`。
形式化陈述：forget : CommGrp C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂Grp_map_hom {A B : CommGrp C} (f : A ⟶ B) :
    ((forget₂Grp C).map f).hom = f.hom.hom :=
  rfl

/-- The forgetful functor from commutative group objects to commutative monoid objects. -/
/-
**CategoryTheory.CommGrp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommGr
p`。
形式化陈述：forget : CommGrp C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from commutative group objects to commutative monoid objec
ts.
-/
def forget₂CommMon : CommGrp C ⥤ CommMon C where
  obj G := CommMon.mk G.X
  map f := CommMon.homMk f.hom.hom

/-- The forgetful functor from commutative group objects to commutative monoid objects is fully
faithful. -/
/-
**CategoryTheory.CommGrp.fullyFaithfulForget** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.CommGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from commutative group objects to commutative monoid objec
ts is fully
faithful.
-/
def fullyFaithfulForget₂CommMon : (forget₂CommMon C).FullyFaithful where
  preimage f := InducedCategory.homMk (Grp.homMk' f.hom)
/-
**CategoryTheory.CommGrp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂CommMon C).Full := (fullyFaithfulForget₂CommMon _).full
/-
**CategoryTheory.CommGrp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂CommMon C).Faithful := (fullyFaithfulForget₂CommMon _).faithful

@[simp]
/-
**CategoryTheory.CommGrp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommGr
p`。
形式化陈述：forget : CommGrp C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂CommMon_obj_one (A : CommGrp C) : η[((forget₂CommMon C).obj A).X] = η[A.X] :=
  rfl

@[simp]
/-
**CategoryTheory.CommGrp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommGr
p`。
形式化陈述：forget : CommGrp C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂CommMon_obj_mul (A : CommGrp C) : μ[((forget₂CommMon C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
/-
**CategoryTheory.CommGrp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommGr
p`。
形式化陈述：forget : CommGrp C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂CommMon_map_hom {A B : CommGrp C} (f : A ⟶ B) :
    ((forget₂CommMon C).map f).hom = f.hom.hom :=
  rfl

/-- The forgetful functor from commutative group objects to the ambient category. -/
@[simps!]
/-
**CategoryTheory.CommGrp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommGr
p`。
形式化陈述：forget : CommGrp C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from commutative group objects to the ambient category.
-/
def forget : CommGrp C ⥤ C :=
  forget₂Grp C ⋙ Grp.forget C
/-
**CategoryTheory.CommGrp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget C).Faithful where

@[simp]
/-
**CategoryTheory.CommGrp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommGr
p`。
形式化陈述：forget : CommGrp C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂Grp_comp_forget : forget₂Grp C ⋙ Grp.forget C = forget C := rfl

@[simp]
/-
**CategoryTheory.CommGrp.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommGr
p`。
形式化陈述：forget : CommGrp C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂CommMon_comp_forget : forget₂CommMon C ⋙ CommMon.forget C = forget C := rfl
/-
**CategoryTheory.CommGrp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G H : CommGrp C} {f : G ⟶ H} [IsIso f] : IsIso f.hom :=
  inferInstanceAs (IsIso ((forget₂Grp C).map f))
/-
**CategoryTheory.CommGrp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G H : CommGrp C} {f : G ⟶ H} [IsIso f] : IsIso f.hom.hom :=
  inferInstanceAs (IsIso ((forget₂Grp C ⋙ Grp.forget₂Mon C).map f))

end

/-- Construct an isomorphism of commutative group objects by giving a monoid isomorphism between the
underlying objects. -/
@[simps!]
/-
**CategoryTheory.CommGrp.mkIso'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommGr
p`。
形式化陈述：mkIso' {G H : C} (e : G ≅ H) [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCom
mMonObj H] [IsMonHom e.hom] : mk G ≅ mk H
参数：e : G ≅ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism of commutative group objects by giving a monoid isomorp
hism between the
underlying objects.
-/
def mkIso' {G H : C} (e : G ≅ H) [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
    [IsMonHom e.hom] : mk G ≅ mk H :=
  (fullyFaithfulForget₂Grp C).preimageIso (Grp.mkIso' e)

section

variable {G H : CommGrp C} (e : G.X ≅ H.X) (one_f : η[G.X] ≫ e.hom = η[H.X] := by cat_disch)
  (mul_f : μ[G.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[H.X] := by cat_disch)

set_option backward.privateInPublic true in
/-- Construct an isomorphism of group objects by giving an isomorphism between the underlying
objects and checking compatibility with unit and multiplication only in the forward direction. -/
/-
**CategoryTheory.CommGrp.mkIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.CommG
rp`。
形式化陈述：mkIso : G ≅ H
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommGrp.comm`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   [inst_2
 : CategoryTheory…

--- 原说明 ---
Construct an isomorphism of group objects by giving an isomorphism between the u
nderlying
objects and checking compatibility with unit and multiplication only in the forw
ard direction.
-/
abbrev mkIso : G ≅ H :=
  have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

set_option backward.privateInPublic true in
/-
**CategoryTheory.CommGrp.mkIso_hom_hom_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.CommGrp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] {G H : CategoryTheory.CommGrp C} (e : G.X ≅ H.X)   (one_f :     autoParam 
(CategoryTheory.CategoryStruct.comp CategoryTheory.MonObj.one e.hom = CategoryTh
eory.MonObj.one)       _auto_100✝)   (mul_f :     autoParam       (CategoryTheor
y.CategoryStruct.comp CategoryTheory.MonObj.mul e.hom =         CategoryTheory.C
ategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.tensorHom e.hom e.hom)
           CategoryTheory.MonObj.mul)       _auto_102✝),   (CategoryTheory.CommG
rp.mkIso e one_f mul_f).hom.hom.hom.hom = e.hom
参数：e : G.X ≅ H.X；one_f :     autoParam (CategoryTheory.CategoryStruct.comp Categ
oryTheory.MonObj.one e.hom = CategoryTheory.MonObj.one)       _auto_100✝；mul_f :
     autoParam       (CategoryTheory.CategoryStruct.comp CategoryTheory.MonObj.m
ul e.hom =         CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCa
tegoryStruct.tensorHom e.hom e.hom)           CategoryTheory.MonObj.mul)       _
auto_102✝；CategoryTheory.CommGrp.mkIso e one_f mul_f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mkIso_hom_hom_hom_hom : (mkIso e one_f mul_f).hom.hom.hom.hom = e.hom := rfl
set_option backward.privateInPublic true in
/-
**CategoryTheory.CommGrp.mkIso_inv_hom_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.CommGrp`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] {G H : CategoryTheory.CommGrp C} (e : G.X ≅ H.X)   (one_f :     autoParam 
(CategoryTheory.CategoryStruct.comp CategoryTheory.MonObj.one e.hom = CategoryTh
eory.MonObj.one)       _auto_105✝)   (mul_f :     autoParam       (CategoryTheor
y.CategoryStruct.comp CategoryTheory.MonObj.mul e.hom =         CategoryTheory.C
ategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.tensorHom e.hom e.hom)
           CategoryTheory.MonObj.mul)       _auto_107✝),   (CategoryTheory.CommG
rp.mkIso e one_f mul_f).inv.hom.hom.hom = e.inv
参数：e : G.X ≅ H.X；one_f :     autoParam (CategoryTheory.CategoryStruct.comp Categ
oryTheory.MonObj.one e.hom = CategoryTheory.MonObj.one)       _auto_105✝；mul_f :
     autoParam       (CategoryTheory.CategoryStruct.comp CategoryTheory.MonObj.m
ul e.hom =         CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCa
tegoryStruct.tensorHom e.hom e.hom)           CategoryTheory.MonObj.mul)       _
auto_107✝；CategoryTheory.CommGrp.mkIso e one_f mul_f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mkIso_inv_hom_hom_hom : (mkIso e one_f mul_f).inv.hom.hom.hom = e.inv := rfl

end

/-
**CategoryTheory.CommGrp.uniqueHomFromTrivial** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.CommGrp`。
形式化陈述：uniqueHomFromTrivial (A : CommGrp C) : Unique (trivial C ⟶ A)
参数：A : CommGrp C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueHomFromTrivial (A : CommGrp C) : Unique (trivial C ⟶ A) :=
  Equiv.unique (show _ ≃ (Grp.trivial C ⟶ A.toGrp) from
    InducedCategory.homEquiv)
/-
**CategoryTheory.CommGrp.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasInitial (CommGrp C) :=
  hasInitial_of_unique (trivial C)

end CommGrp

variable {C}
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianMonoidalCategory E] [BraidedCategory E]

namespace Functor
variable {F F' : C ⥤ D} [F.Braided] [F'.Braided] {G : D ⥤ E} [G.Braided]

open Monoidal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- A finite-product-preserving functor takes commutative group objects to commutative group
objects. -/
@[simps!]
/-
**CategoryTheory.Functor.mapCommGrp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：mapCommGrp : CommGrp C ⥤ CommGrp D where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite-product-preserving functor takes commutative group objects to commutati
ve group
objects.
-/
def mapCommGrp : CommGrp C ⥤ CommGrp D where
  obj A :=
    { F.mapGrp.obj A.toGrp with
      comm :=
        { mul_comm := by
            dsimp
            rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommMonObj.mul_comm] } }
  map f := InducedCategory.homMk (F.mapGrp.map f.hom)
/-
**CategoryTheory.Functor.Faithful.mapCommGrp** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor.Faithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] {D : Type u₂} [inst_3 : CategoryTheory.Category.{v₂, u₂} D]   [inst_4 : Ca
tegoryTheory.CartesianMonoidalCategory D] [inst_5 : CategoryTheory.BraidedCatego
ry D]   {F : CategoryTheory.Functor C D} [inst_6 : F.Braided] [F.Faithful], F.ma
pCommGrp.Faithful
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Functor.Faithful.comp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.CommGrp.instFaithfulForget`：∀ (C : Type u₁) [inst : Categ
oryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidalCategor
y C]   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
-/
protected instance Faithful.mapCommGrp [F.Faithful] : F.mapCommGrp.Faithful where
  map_injective hfg :=
    (CommGrp.forget _ ⋙ F).map_injective ((CommGrp.forget _).congr_map hfg)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then
`CommGrpCat(F) : CommGrpCat C ⥤ CommGrpCat D` is fully faithful too. -/
@[simps]
/-
**CategoryTheory.Functor.FullyFaithful.mapCommGrp** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor.FullyFaithful`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       [inst_2 : CategoryTheory
.BraidedCategory C] →         {D : Type u₂} →           [inst_3 : CategoryTheory
.Category.{v₂, u₂} D] →             [inst_4 : CategoryTheory.CartesianMonoidalCa
tegory D] →               [inst_5 : CategoryTheory.BraidedCategory D] →         
        {F : CategoryTheory.Functor C D} → [inst_6 : F.Braided] → F.FullyFaithfu
l → F.mapCommGrp.FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` is a fully faithful monoidal functor, then
`CommGrpCat(F) : CommGrpCat C ⥤ CommGrpCat D` is fully faithful too.
-/
protected def FullyFaithful.mapCommGrp (hF : F.FullyFaithful) : F.mapCommGrp.FullyFaithful where
  preimage f := InducedCategory.homMk (Grp.homMk' (hF.mapMon.preimage f.hom.hom))
/-
**CategoryTheory.Functor.Full.mapCommGrp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor.Full`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCatego
ry C] {D : Type u₂} [inst_3 : CategoryTheory.Category.{v₂, u₂} D]   [inst_4 : Ca
tegoryTheory.CartesianMonoidalCategory D] [inst_5 : CategoryTheory.BraidedCatego
ry D]   {F : CategoryTheory.Functor C D} [inst_6 : F.Braided] [F.Full] [F.Faithf
ul], F.mapCommGrp.Full
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
protected instance Full.mapCommGrp [F.Full] [F.Faithful] : F.mapCommGrp.Full :=
  (FullyFaithful.ofFullyFaithful F).mapCommGrp.full

@[simp]
/-
**CategoryTheory.Functor.mapCommGrp_id_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapCommGrp_id_one (A : CommGrp C) : η[((𝟭 C).mapCommGrp.obj A).X] = 𝟙 _ ≫ 
η[A.X]
参数：A : CommGrp C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapCommGrp_id_one (A : CommGrp C) :
    η[((𝟭 C).mapCommGrp.obj A).X] = 𝟙 _ ≫ η[A.X] :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.mapCommpGrp_id_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：mapCommpGrp_id_mul (A : CommGrp C) : μ[((𝟭 C).mapCommGrp.obj A).X] = 𝟙 _ ≫
 μ[A.X]
参数：A : CommGrp C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapCommpGrp_id_mul (A : CommGrp C) :
    μ[((𝟭 C).mapCommGrp.obj A).X] = 𝟙 _ ≫ μ[A.X] :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.comp_mapCommGrp_one** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：comp_mapCommGrp_one (A : CommGrp C) : η[((F ⋙ G).mapCommGrp.obj A).X] = La
xMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X]
参数：A : CommGrp C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_mapCommGrp_one (A : CommGrp C) :
    η[((F ⋙ G).mapCommGrp.obj A).X] = LaxMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X] :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.comp_mapCommGrp_mul** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：comp_mapCommGrp_mul (A : CommGrp C) : μ[((F ⋙ G).mapCommGrp.obj A).X] = La
xMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X]
参数：A : CommGrp C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_mapCommGrp_mul (A : CommGrp C) :
    μ[((F ⋙ G).mapCommGrp.obj A).X] = LaxMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X] :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity functor is also the identity on commutative group objects. -/
@[simps!]
/-
**CategoryTheory.Functor.mapCommGrpIdIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：mapCommGrpIdIso : mapCommGrp (𝟭 C) ≅ 𝟭 (CommGrp C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity functor is also the identity on commutative group objects.
-/
def mapCommGrpIdIso : mapCommGrp (𝟭 C) ≅ 𝟭 (CommGrp C) :=
  NatIso.ofComponents (fun X ↦ CommGrp.mkIso (.refl _) (by simp)
    (by simp))

set_option backward.isDefEq.respectTransparency false in
/-- The composition functor is also the composition on commutative group objects. -/
@[simps!]
/-
**CategoryTheory.Functor.mapCommGrpCompIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapCommGrpCompIso : (F ⋙ G).mapCommGrp ≅ F.mapCommGrp ⋙ G.mapCommGrp
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition functor is also the composition on commutative group objects.
-/
def mapCommGrpCompIso : (F ⋙ G).mapCommGrp ≅ F.mapCommGrp ⋙ G.mapCommGrp :=
  NatIso.ofComponents fun X ↦ CommGrp.mkIso (.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Natural transformations between functors lift to commutative group objects. -/
@[simps!]
/-
**CategoryTheory.Functor.mapCommGrpNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：mapCommGrpNatTrans (f : F ⟶ F') : F.mapCommGrp ⟶ F'.mapCommGrp where app X
参数：f : F ⟶ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Natural transformations between functors lift to commutative group objects.
-/
def mapCommGrpNatTrans (f : F ⟶ F') : F.mapCommGrp ⟶ F'.mapCommGrp where
  app X := InducedCategory.homMk ((mapGrpNatTrans f).app X.toGrp)

set_option backward.isDefEq.respectTransparency false in
/-- Natural isomorphisms between functors lift to commutative group objects. -/
@[simps!]
/-
**CategoryTheory.Functor.mapCommGrpNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：mapCommGrpNatIso (e : F ≅ F') : F.mapCommGrp ≅ F'.mapCommGrp
参数：e : F ≅ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Natural isomorphisms between functors lift to commutative group objects.
-/
def mapCommGrpNatIso (e : F ≅ F') : F.mapCommGrp ≅ F'.mapCommGrp :=
  NatIso.ofComponents fun X ↦ CommGrp.mkIso (e.app _)

attribute [local instance] Functor.Braided.ofChosenFiniteProducts in
/-- `mapCommGrp` is functorial in the left-exact functor. -/
@[simps]
/-
**CategoryTheory.Functor.mapCommGrpFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapCommGrpFunctor : (C ⥤ₗ D) ⥤ CommGrp C ⥤ CommGrp D where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mapCommGrp` is functorial in the left-exact functor.
-/
noncomputable def mapCommGrpFunctor : (C ⥤ₗ D) ⥤ CommGrp C ⥤ CommGrp D where
  obj F := F.1.mapCommGrp
  map α := mapCommGrpNatTrans α.hom

end Functor

open CategoryTheory.Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Braided] [G.Braided]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An adjunction of braided functors lifts to an adjunction of their lifts to commutative group
objects. -/
/-
**CategoryTheory.Adjunction.mapCommGrp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Adjunction`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       [inst_2 : CategoryTheory
.BraidedCategory C] →         {D : Type u₂} →           [inst_3 : CategoryTheory
.Category.{v₂, u₂} D] →             [inst_4 : CategoryTheory.CartesianMonoidalCa
tegory D] →               [inst_5 : CategoryTheory.BraidedCategory D] →         
        {F : CategoryTheory.Functor C D} →                   {G : CategoryTheory
.Functor D C} →                     (F ⊣ G) → [inst_6 : F.Braided] → [inst_7 : G
.Braided] → F.mapCommGrp ⊣ G.mapCommGrp
参数：F ⊣ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An adjunction of braided functors lifts to an adjunction of their lifts to commu
tative group
objects.
-/
@[simps] noncomputable def mapCommGrp : F.mapCommGrp ⊣ G.mapCommGrp where
  unit := mapCommGrpIdIso.inv ≫ mapCommGrpNatTrans a.unit ≫ mapCommGrpCompIso.hom
  counit := mapCommGrpCompIso.inv ≫ mapCommGrpNatTrans a.counit ≫ mapCommGrpIdIso.hom

end Adjunction

namespace Equivalence
variable (e : C ≌ D) [e.functor.Braided] [e.inverse.Braided]

set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories lifts to an equivalence of their commutative group objects. -/
/-
**CategoryTheory.Equivalence.mapCommGrp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Equivalence`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       [inst_2 : CategoryTheory
.BraidedCategory C] →         {D : Type u₂} →           [inst_3 : CategoryTheory
.Category.{v₂, u₂} D] →             [inst_4 : CategoryTheory.CartesianMonoidalCa
tegory D] →               [inst_5 : CategoryTheory.BraidedCategory D] →         
        (e : C ≌ D) →                   [e.functor.Braided] → [e.inverse.Braided
] → CategoryTheory.CommGrp C ≌ CategoryTheory.CommGrp D
参数：e : C ≌ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of categories lifts to an equivalence of their commutative group 
objects.
-/
@[simps] noncomputable def mapCommGrp : CommGrp C ≌ CommGrp D where
  functor := e.functor.mapCommGrp
  inverse := e.inverse.mapCommGrp
  unitIso := mapCommGrpIdIso.symm ≪≫ mapCommGrpNatIso e.unitIso ≪≫ mapCommGrpCompIso
  counitIso := mapCommGrpCompIso.symm ≪≫ mapCommGrpNatIso e.counitIso ≪≫ mapCommGrpIdIso

end CategoryTheory.Equivalence

