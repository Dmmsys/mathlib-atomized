/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Forget

/-!
# Differential objects in a category.

A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : obj ⟶ obj⟦1⟧`, such that `d^2 = 0`.

We build the category of differential objects, and some basic constructions
such as the forgetful functor, zero morphisms and zero objects, and the shift functor
on differential objects.
-/

@[expose] public section


open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (S : Type*) [AddMonoidWithOne S] (C : Type u) [Category.{v} C]
variable [HasZeroMorphisms C] [HasShift C S]

/-- A differential object in a category with zero morphisms and a shift is
an object `obj` equipped with
a morphism `d : obj ⟶ obj⟦1⟧`, such that `d^2 = 0`. -/
/-
**CategoryTheory.DifferentialObject** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：DifferentialObject where /-- The underlying object of a differential objec
t. -/ obj : C /-- The differential of a differential object. -/ d : obj ⟶ obj⟦(1
 : S)⟧ /-- The differential `d` satisfies that `d² = 0`. -/ d_squared : d ≫ d⟦(1
 : S)⟧' = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A differential object in a category with zero morphisms and a shift is
an object `obj` equipped with
a morphism `d : obj ⟶ obj⟦1⟧`, such that `d^2 = 0`.
-/
structure DifferentialObject where
  /-- The underlying object of a differential object. -/
  obj : C
  /-- The differential of a differential object. -/
  d : obj ⟶ obj⟦(1 : S)⟧
  /-- The differential `d` satisfies that `d² = 0`. -/
  d_squared : d ≫ d⟦(1 : S)⟧' = 0 := by cat_disch

attribute [reassoc (attr := simp)] DifferentialObject.d_squared

variable {S C}

namespace DifferentialObject

/-- A morphism of differential objects is a morphism commuting with the differentials. -/
@[ext]
/-
**CategoryTheory.DifferentialObject.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheor
y.DifferentialObject`。
形式化陈述：Hom (X Y : DifferentialObject S C) where /-- The morphism between underlyi
ng objects of the two differentiable objects. -/ f : X.obj ⟶ Y.obj comm : X.d ≫ 
f⟦1⟧' = f ≫ Y.d
参数：X Y : DifferentialObject S C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of differential objects is a morphism commuting with the differential
s.
-/
structure Hom (X Y : DifferentialObject S C) where
  /-- The morphism between underlying objects of the two differentiable objects. -/
  f : X.obj ⟶ Y.obj
  comm : X.d ≫ f⟦1⟧' = f ≫ Y.d := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

namespace Hom

/-- The identity morphism of a differential object. -/
@[simps]
/-
**CategoryTheory.DifferentialObject.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.DifferentialObject.Hom`。
形式化陈述：id (X : DifferentialObject S C) : Hom X X where f
参数：X : DifferentialObject S C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism of a differential object.
-/
def id (X : DifferentialObject S C) : Hom X X where
  f := 𝟙 X.obj

/-- The composition of morphisms of differential objects. -/
@[simps]
/-
**CategoryTheory.DifferentialObject.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.DifferentialObject.Hom`。
形式化陈述：comp {X Y Z : DifferentialObject S C} (f : Hom X Y) (g : Hom Y Z) : Hom X 
Z where f
参数：f : Hom X Y；g : Hom Y Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of morphisms of differential objects.
-/
def comp {X Y Z : DifferentialObject S C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  f := f.f ≫ g.f

end Hom

/-
**CategoryTheory.DifferentialObject.categoryOfDifferentialObjects** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.DifferentialObject`。
形式化陈述：categoryOfDifferentialObjects : Category (DifferentialObject S C) where Ho
m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance categoryOfDifferentialObjects : Category (DifferentialObject S C) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g

@[ext]
/-
**CategoryTheory.DifferentialObject.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.DifferentialObject`。
形式化陈述：ext {A B : DifferentialObject S C} {f g : A ⟶ B} (w : f.f = g.f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.DifferentialObject.Hom.ext`：∀ {S : Type u_1} {inst : AddM
onoidWithOne S} {C : Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst
_2 : CategoryTheory.Limits.HasZ…
-/
theorem ext {A B : DifferentialObject S C} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch) : f = g :=
  Hom.ext w

@[simp]
/-
**CategoryTheory.DifferentialObject.id_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.DifferentialObject`。
形式化陈述：id_f (X : DifferentialObject S C) : (𝟙 X : X ⟶ X).f = 𝟙 X.obj
参数：X : DifferentialObject S C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_f (X : DifferentialObject S C) : (𝟙 X : X ⟶ X).f = 𝟙 X.obj := rfl

@[simp]
/-
**CategoryTheory.DifferentialObject.comp_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.DifferentialObject`。
形式化陈述：comp_f {X Y Z : DifferentialObject S C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).
f = f.f ≫ g.f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_f {X Y Z : DifferentialObject S C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).f = f.f ≫ g.f :=
  rfl

@[simp]
/-
**CategoryTheory.DifferentialObject.eqToHom_f** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.DifferentialObject`。
形式化陈述：eqToHom_f {X Y : DifferentialObject S C} (h : X = Y) : Hom.f (eqToHom h) =
 eqToHom (congr_arg _ h)
参数：h : X = Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
-/
theorem eqToHom_f {X Y : DifferentialObject S C} (h : X = Y) :
    Hom.f (eqToHom h) = eqToHom (congr_arg _ h) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl]
  rfl

variable (S C)

/-- The forgetful functor taking a differential object to its underlying object. -/
/-
**CategoryTheory.DifferentialObject.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.DifferentialObject`。
形式化陈述：forget : DifferentialObject S C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor taking a differential object to its underlying object.
-/
def forget : DifferentialObject S C ⥤ C where
  obj X := X.obj
  map f := f.f
/-
**CategoryTheory.DifferentialObject.forget_faithful** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.DifferentialObject`。
形式化陈述：∀ (S : Type u_1) [inst : AddMonoidWithOne S] (C : Type u) [inst_1 : Catego
ryTheory.Category.{v, u} C]   [inst_2 : CategoryTheory.Limits.HasZeroMorphisms C
] [inst_3 : CategoryTheory.HasShift C S],   (CategoryTheory.DifferentialObject.f
orget S C).Faithful
参数：S : Type u_1；C : Type u；CategoryTheory.DifferentialObject.forget S C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.DifferentialObject.ext`：ext {A B : DifferentialObject S C
} {f g : A ⟶ B} (w : f.f = g.f
-/
instance forget_faithful : (forget S C).Faithful where

variable {S C}

section
variable [(shiftFunctor C (1 : S)).PreservesZeroMorphisms]

/-
**CategoryTheory.DifferentialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.D
ifferentialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : DifferentialObject S C} : Zero (X ⟶ Y) := ⟨{f := 0}⟩

@[simp]
/-
**CategoryTheory.DifferentialObject.zero_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.DifferentialObject`。
形式化陈述：zero_f (P Q : DifferentialObject S C) : (0 : P ⟶ Q).f = 0
参数：P Q : DifferentialObject S C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_f (P Q : DifferentialObject S C) : (0 : P ⟶ Q).f = 0 := rfl
/-
**CategoryTheory.DifferentialObject.hasZeroMorphisms** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.DifferentialObject`。
形式化陈述：{S : Type u_1} →   [inst : AddMonoidWithOne S] →     {C : Type u} →       
[inst_1 : CategoryTheory.Category.{v, u} C] →         [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C] →           [inst_3 : CategoryTheory.HasShift C S] →  
           [(CategoryTheory.shiftFunctor C 1).PreservesZeroMorphisms] →         
      CategoryTheory.Limits.HasZeroMorphisms (CategoryTheory.DifferentialObject 
S C)
参数：CategoryTheory.shiftFunctor C 1；CategoryTheory.DifferentialObject S C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasZeroMorphisms : HasZeroMorphisms (DifferentialObject S C) where

end

/-- An isomorphism of differential objects gives an isomorphism of the underlying objects. -/
@[simps]
/-
**CategoryTheory.DifferentialObject.isoApp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.DifferentialObject`。
形式化陈述：isoApp {X Y : DifferentialObject S C} (f : X ≅ Y) : X.obj ≅ Y.obj where ho
m
参数：f : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of differential objects gives an isomorphism of the underlying ob
jects.
-/
def isoApp {X Y : DifferentialObject S C} (f : X ≅ Y) : X.obj ≅ Y.obj where
  hom := f.hom.f
  inv := f.inv.f
  hom_inv_id := by rw [← comp_f, Iso.hom_inv_id, id_f]
  inv_hom_id := by rw [← comp_f, Iso.inv_hom_id, id_f]

@[simp]
/-
**CategoryTheory.DifferentialObject.isoApp_refl** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.DifferentialObject`。
形式化陈述：isoApp_refl (X : DifferentialObject S C) : isoApp (Iso.refl X) = Iso.refl 
X.obj
参数：X : DifferentialObject S C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoApp_refl (X : DifferentialObject S C) : isoApp (Iso.refl X) = Iso.refl X.obj := rfl

@[simp]
/-
**CategoryTheory.DifferentialObject.isoApp_symm** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.DifferentialObject`。
形式化陈述：isoApp_symm {X Y : DifferentialObject S C} (f : X ≅ Y) : isoApp f.symm = (
isoApp f).symm
参数：f : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoApp_symm {X Y : DifferentialObject S C} (f : X ≅ Y) : isoApp f.symm = (isoApp f).symm :=
  rfl

@[simp]
/-
**CategoryTheory.DifferentialObject.isoApp_trans** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.DifferentialObject`。
形式化陈述：isoApp_trans {X Y Z : DifferentialObject S C} (f : X ≅ Y) (g : Y ≅ Z) : is
oApp (f ≪≫ g) = isoApp f ≪≫ isoApp g
参数：f : X ≅ Y；g : Y ≅ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoApp_trans {X Y Z : DifferentialObject S C} (f : X ≅ Y) (g : Y ≅ Z) :
    isoApp (f ≪≫ g) = isoApp f ≪≫ isoApp g := rfl

/-- An isomorphism of differential objects can be constructed
from an isomorphism of the underlying objects that commutes with the differentials. -/
@[simps]
/-
**CategoryTheory.DifferentialObject.mkIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.DifferentialObject`。
形式化陈述：mkIso {X Y : DifferentialObject S C} (f : X.obj ≅ Y.obj) (hf : X.d ≫ f.hom
⟦1⟧' = f.hom ≫ Y.d) : X ≅ Y where hom
参数：f : X.obj ≅ Y.obj；hf : X.d ≫ f.hom⟦1⟧' = f.hom ≫ Y.d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of differential objects can be constructed
from an isomorphism of the underlying objects that commutes with the differentia
ls.
-/
def mkIso {X Y : DifferentialObject S C} (f : X.obj ≅ Y.obj) (hf : X.d ≫ f.hom⟦1⟧' = f.hom ≫ Y.d) :
    X ≅ Y where
  hom := ⟨f.hom, hf⟩
  inv := ⟨f.inv, by
    rw [← Functor.mapIso_inv, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, Functor.mapIso_hom,
      hf]⟩
  hom_inv_id := by ext1; dsimp; exact f.hom_inv_id
  inv_hom_id := by ext1; dsimp; exact f.inv_hom_id

end DifferentialObject

namespace Functor

universe v' u'

variable (D : Type u') [Category.{v'} D]
variable [HasZeroMorphisms D] [HasShift D S]

set_option backward.isDefEq.respectTransparency false in
/-- A functor `F : C ⥤ D` which commutes with shift functors on `C` and `D` and preserves zero
morphisms can be lifted to a functor `DifferentialObject S C ⥤ DifferentialObject S D`. -/
@[simps]
/-
**CategoryTheory.Functor.mapDifferentialObject** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：mapDifferentialObject (F : C ⥤ D) (η : (shiftFunctor C (1 : S)).comp F ⟶ F
.comp (shiftFunctor D (1 : S))) (hF : forall c c', F.map (0 : c ⟶ c') = 0) : Dif
ferentialObject S C ⥤ DifferentialObject S D where obj X
参数：F : C ⥤ D；η : (shiftFunctor C (1 : S)).comp F ⟶ F.comp (shiftFunctor D (1 : S
))；hF : forall c c', F.map (0 : c ⟶ c') = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` which commutes with shift functors on `C` and `D` and pres
erves zero
morphisms can be lifted to a functor `DifferentialObject S C ⥤ DifferentialObjec
t S D`.
-/
def mapDifferentialObject (F : C ⥤ D)
    (η : (shiftFunctor C (1 : S)).comp F ⟶ F.comp (shiftFunctor D (1 : S)))
    (hF : ∀ c c', F.map (0 : c ⟶ c') = 0) : DifferentialObject S C ⥤ DifferentialObject S D where
  obj X :=
    { obj := F.obj X.obj
      d := F.map X.d ≫ η.app X.obj
      d_squared := by
        rw [Functor.map_comp, ← Functor.comp_map F (shiftFunctor D (1 : S))]
        slice_lhs 2 3 => rw [← η.naturality X.d]
        rw [Functor.comp_map]
        slice_lhs 1 2 => rw [← F.map_comp, X.d_squared, hF]
        rw [zero_comp, zero_comp] }
  map f :=
    { f := F.map f.f
      comm := by
        dsimp
        slice_lhs 2 3 => rw [← Functor.comp_map F (shiftFunctor D (1 : S)), ← η.naturality f.f]
        slice_lhs 1 2 => rw [Functor.comp_map, ← F.map_comp, f.comm, F.map_comp]
        rw [Category.assoc] }
  map_id := by intros; ext; simp
  map_comp := by intros; ext; simp

end Functor

end CategoryTheory

namespace CategoryTheory

namespace DifferentialObject

variable (S : Type*) [AddMonoidWithOne S] (C : Type u) [Category.{v} C]
variable [HasZeroObject C] [HasZeroMorphisms C] [HasShift C S]
variable [(shiftFunctor C (1 : S)).PreservesZeroMorphisms]

open scoped ZeroObject

/-
**CategoryTheory.DifferentialObject.hasZeroObject** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.DifferentialObject`。
形式化陈述：hasZeroObject : HasZeroObject (DifferentialObject S C) where zero
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.DifferentialObject.ext`：ext {A B : DifferentialObject S C
} {f g : A ⟶ B} (w : f.f = g.f
· 使用定理 `CategoryTheory.Limits.HasZeroObject.from_zero_ext`：from_zero_ext {X : C}
 (f g : 0 ⟶ X) : f = g
· 使用定理 `CategoryTheory.Limits.HasZeroObject.to_zero_ext`：to_zero_ext {X : C} (f 
g : X ⟶ 0) : f = g
-/
instance hasZeroObject : HasZeroObject (DifferentialObject S C) where
  zero := ⟨{ obj := 0, d := 0 },
    { unique_to := fun X => ⟨⟨⟨{ f := 0 }⟩, fun f => by ext⟩⟩,
      unique_from := fun X => ⟨⟨⟨{ f := 0 }⟩, fun f => by ext⟩⟩ }⟩

end DifferentialObject

namespace DifferentialObject

section ConcreteCategory

variable (S : Type*) [AddMonoidWithOne S]
variable (C : Type (u + 1)) [LargeCategory C] [HasZeroMorphisms C]
variable {FC : C → C → Type*} {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory C FC] [HasShift C S]

/--
The type of `C`-morphisms that can be lifted back to morphisms in the category `DifferentialObject`.
-/
/-
**CategoryTheory.DifferentialObject.HomSubtype** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.DifferentialObject`。
形式化陈述：HomSubtype (X Y : DifferentialObject S C)
参数：X Y : DifferentialObject S C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `C`-morphisms that can be lifted back to morphisms in the category `
DifferentialObject`.
-/
abbrev HomSubtype (X Y : DifferentialObject S C) :=
  { f : FC X.obj Y.obj // X.d ≫ (ConcreteCategory.ofHom f)⟦1⟧' = (ConcreteCategory.ofHom f) ≫ Y.d }
/-
**CategoryTheory.DifferentialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.D
ifferentialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : DifferentialObject S C) :
    FunLike (HomSubtype S C X Y) (CC X.obj) (CC Y.obj) where
  coe f := f.1
  coe_injective _ _ h := Subtype.ext (DFunLike.coe_injective h)
/-
**CategoryTheory.DifferentialObject.concreteCategoryOfDifferentialObjects** 是 Ma
thlib 中的一个实例，位于命名空间 `CategoryTheory.DifferentialObject`。
形式化陈述：concreteCategoryOfDifferentialObjects : ConcreteCategory (DifferentialObje
ct S C) (HomSubtype S C) where hom f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance concreteCategoryOfDifferentialObjects :
    ConcreteCategory (DifferentialObject S C) (HomSubtype S C) where
  hom f := ⟨ConcreteCategory.hom (C := C) f.1, by simp [ConcreteCategory.ofHom_hom]⟩
  ofHom f := ⟨ConcreteCategory.ofHom (C := C) f, by simpa [ConcreteCategory.hom_ofHom] using f.2⟩
  hom_ofHom _ := by dsimp; ext; simp [ConcreteCategory.hom_ofHom]
  ofHom_hom _ := by ext; simp [ConcreteCategory.ofHom_hom]
  id_apply := ConcreteCategory.id_apply (C := C)
  comp_apply _ _ := ConcreteCategory.comp_apply (C := C) _ _
/-
**CategoryTheory.DifferentialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.D
ifferentialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasForget₂ (DifferentialObject S C) C where
  forget₂ := forget S C

end ConcreteCategory

end DifferentialObject

/-! The category of differential objects itself has a shift functor. -/


namespace DifferentialObject

variable {S : Type*} [AddCommGroupWithOne S] (C : Type u) [Category.{v} C]
variable [HasZeroMorphisms C] [HasShift C S]

noncomputable section

set_option backward.defeqAttrib.useBackward true in
/-- The shift functor on `DifferentialObject S C`. -/
@[simps]
/-
**CategoryTheory.DifferentialObject.shiftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.DifferentialObject`。
形式化陈述：shiftFunctor (n : S) : DifferentialObject S C ⥤ DifferentialObject S C whe
re obj X
参数：n : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shift functor on `DifferentialObject S C`.
-/
def shiftFunctor (n : S) : DifferentialObject S C ⥤ DifferentialObject S C where
  obj X :=
    { obj := X.obj⟦n⟧
      d := X.d⟦n⟧' ≫ (shiftComm _ _ _).hom
      d_squared := by
        rw [Functor.map_comp, Category.assoc, shiftComm_hom_comp_assoc, ← Functor.map_comp_assoc,
          X.d_squared, Functor.map_zero, zero_comp] }
  map f :=
    { f := f.f⟦n⟧'
      comm := by
        dsimp
        rw [Category.assoc]
        erw [shiftComm_hom_comp]
        rw [← Functor.map_comp_assoc, f.comm, Functor.map_comp_assoc]
        rfl }
  map_id X := by ext1; dsimp; rw [Functor.map_id]
  map_comp f g := by ext1; dsimp; rw [Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
/-- The shift functor on `DifferentialObject S C` is additive. -/
@[simps!]
nonrec def shiftFunctorAdd (m n : S) :
    shiftFunctor C (m + n) ≅ shiftFunctor C m ⋙ shiftFunctor C n := by
  refine NatIso.ofComponents (fun X => mkIso (shiftAdd X.obj _ _) ?_) (fun f => ?_)
  · dsimp
    rw [← cancel_epi ((shiftFunctorAdd C m n).inv.app X.obj)]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← NatTrans.naturality_assoc]
    dsimp
    simp only [Functor.map_comp, Category.assoc,
      shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app 1 m n X.obj,
      Iso.inv_hom_id_app_assoc]
  · ext; dsimp; exact NatTrans.naturality _ _

section

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The shift by zero is naturally isomorphic to the identity. -/
@[simps!]
/-
**CategoryTheory.DifferentialObject.shiftZero** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.DifferentialObject`。
形式化陈述：shiftZero : shiftFunctor C (0 : S) ≅ 𝟭 (DifferentialObject S C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shift by zero is naturally isomorphic to the identity.
-/
def shiftZero : shiftFunctor C (0 : S) ≅ 𝟭 (DifferentialObject S C) := by
  refine NatIso.ofComponents (fun X => mkIso ((shiftFunctorZero C S).app X.obj) ?_) (fun f => ?_)
  · erw [← NatTrans.naturality]
    dsimp
    simp only [shiftFunctorZero_hom_app_shift, Category.assoc]
  · cat_disch

end

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.DifferentialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.D
ifferentialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasShift (DifferentialObject S C) S :=
  hasShiftMk _ _
    { F := shiftFunctor C
      zero := shiftZero C
      add := shiftFunctorAdd C
      assoc_hom_app := fun m₁ m₂ m₃ X => by
        ext1
        convert! shiftFunctorAdd_assoc_hom_app m₁ m₂ m₃ X.obj
        dsimp [shiftFunctorAdd']
        simp
      zero_add_hom_app := fun n X => by
        ext1
        convert! shiftFunctorAdd_zero_add_hom_app n X.obj
        simp
      add_zero_hom_app := fun n X => by
        ext1
        convert! shiftFunctorAdd_add_zero_hom_app n X.obj
        simp }

end

end DifferentialObject

end CategoryTheory

