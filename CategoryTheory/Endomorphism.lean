/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Kim Morrison, Simon Hudon
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.CategoryTheory.Groupoid

/-!
# Endomorphisms

Definition and basic properties of endomorphisms and automorphisms of an object in a category.

For each `X : C`, we provide `CategoryTheory.End X := X ⟶ X` with a monoid structure,
and `CategoryTheory.Aut X := X ≅ X` with a group structure.
-/

@[expose] public section


universe v v' u u'

namespace CategoryTheory

/-- Endomorphisms of an object in a category. Arguments order in multiplication agrees with
`Function.comp`, not with `CategoryTheory.CategoryStruct.comp`. -/
@[implicit_reducible]
/-
**CategoryTheory.End** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：End {C : Type u} [CategoryStruct.{v} C] (X : C)
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Endomorphisms of an object in a category. Arguments order in multiplication agre
es with
`Function.comp`, not with `CategoryTheory.CategoryStruct.comp`.
-/
def End {C : Type u} [CategoryStruct.{v} C] (X : C) := X ⟶ X

namespace End

section Struct

variable {C : Type u} [CategoryStruct.{v} C] (X : C)

/-
**CategoryTheory.End.one** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.End`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.CategoryStruct.{v, u} C] → (X : C) →
 One (CategoryTheory.End X)
参数：X : C；CategoryTheory.End X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance one : One (End X) := ⟨𝟙 X⟩
/-
**CategoryTheory.End.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.End`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.CategoryStruct.{v, u} C] → (X : C) →
 Inhabited (CategoryTheory.End X)
参数：X : C；CategoryTheory.End X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance inhabited : Inhabited (End X) := ⟨𝟙 X⟩

/-- Multiplication of endomorphisms agrees with `Function.comp`, not with
`CategoryTheory.CategoryStruct.comp`. -/
/-
**CategoryTheory.End.mul** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.End`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.CategoryStruct.{v, u} C] → (X : C) →
 Mul (CategoryTheory.End X)
参数：X : C；CategoryTheory.End X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of endomorphisms agrees with `Function.comp`, not with
`CategoryTheory.CategoryStruct.comp`.
-/
protected instance mul : Mul (End X) := ⟨fun x y => y ≫ x⟩

variable {X}

/-- Assist the typechecker by expressing a morphism `X ⟶ X` as a term of `CategoryTheory.End X`. -/
/-
**CategoryTheory.End.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.End`。
形式化陈述：of (f : X ⟶ X) : End X
参数：f : X ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assist the typechecker by expressing a morphism `X ⟶ X` as a term of `CategoryTh
eory.End X`.
-/
abbrev of (f : X ⟶ X) : End X := f

/-- Assist the typechecker by expressing an endomorphism `f : CategoryTheory.End X` as a term of
`X ⟶ X`. -/
/-
**CategoryTheory.End.asHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.End`。
形式化陈述：asHom (f : End X) : X ⟶ X
参数：f : End X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assist the typechecker by expressing an endomorphism `f : CategoryTheory.End X` 
as a term of
`X ⟶ X`.
-/
abbrev asHom (f : End X) : X ⟶ X := f

-- TODO: to fix defeq abuse, this should be `(1 : End x) = of (𝟙 X)`.
-- But that would require many more extra simp lemmas to get rid of the `of`.
@[simp]
/-
**CategoryTheory.End.one_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.End`。
形式化陈述：one_def : (1 : End X) = 𝟙 X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : End X) = 𝟙 X := rfl

-- TODO: to fix defeq abuse, this should be `xs * ys = of (ys ≫ xs)`.
-- But that would require many more extra simp lemmas to get rid of the `of`.
@[simp]
/-
**CategoryTheory.End.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.End`。
形式化陈述：mul_def (xs ys : End X) : xs * ys = ys ≫ xs
参数：xs ys : End X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (xs ys : End X) : xs * ys = ys ≫ xs := rfl
/-
**CategoryTheory.End.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.End`。
形式化陈述：ext {x y : End X} (h : asHom x = asHom y) : x = y
参数：h : asHom x = asHom y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ext {x y : End X} (h : asHom x = asHom y) : x = y := h

end Struct

/-- Endomorphisms of an object form a monoid -/
/-
**CategoryTheory.End.monoid** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.End`。
形式化陈述：monoid {C : Type u} [Category.{v} C] {X : C} : Monoid (End X) where mul_on
e
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
Endomorphisms of an object form a monoid
-/
instance monoid {C : Type u} [Category.{v} C] {X : C} : Monoid (End X) where
  mul_one := Category.id_comp
  one_mul := Category.comp_id
  mul_assoc := fun x y z => (Category.assoc z y x).symm

section MulAction

variable {C : Type u} [Category.{v} C]

open Opposite

/-
**CategoryTheory.End.mulActionRight** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.En
d`。
形式化陈述：mulActionRight {X Y : C} : MulAction (End Y) (X ⟶ Y) where smul r f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
instance mulActionRight {X Y : C} : MulAction (End Y) (X ⟶ Y) where
  smul r f := f ≫ r
  one_smul := Category.comp_id
  mul_smul _ _ _ := Eq.symm <| Category.assoc _ _ _
/-
**CategoryTheory.End.mulActionLeft** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.End
`。
形式化陈述：mulActionLeft {X Y : C} : MulAction (End X)ᵐᵒᵖ (X ⟶ Y) where smul r f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
instance mulActionLeft {X Y : C} : MulAction (End X)ᵐᵒᵖ (X ⟶ Y) where
  smul r f := r.unop ≫ f
  one_smul := Category.id_comp
  mul_smul _ _ _ := Category.assoc _ _ _
/-
**CategoryTheory.End.smul_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.End`。
形式化陈述：smul_right {X Y : C} {r : End Y} {f : X ⟶ Y} : r • f = f ≫ r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_right {X Y : C} {r : End Y} {f : X ⟶ Y} : r • f = f ≫ r :=
  rfl
/-
**CategoryTheory.End.smul_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.End`。
形式化陈述：smul_left {X Y : C} {r : (End X)ᵐᵒᵖ} {f : X ⟶ Y} : r • f = r.unop ≫ f
参数：End X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_left {X Y : C} {r : (End X)ᵐᵒᵖ} {f : X ⟶ Y} : r • f = r.unop ≫ f :=
  rfl

end MulAction

/-- In a groupoid, endomorphisms form a group -/
/-
**CategoryTheory.End.group** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.End`。
形式化陈述：group {C : Type u} [Groupoid.{v} C] (X : C) : Group (End X) where inv_mul_
cancel
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Groupoid.comp_inv`：∀ {obj : Type u} [self : CategoryTheor
y.Groupoid obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp f 
(CategoryTheory.Groupo…

--- 原说明 ---
In a groupoid, endomorphisms form a group
-/
instance group {C : Type u} [Groupoid.{v} C] (X : C) : Group (End X) where
  inv_mul_cancel := Groupoid.comp_inv
  inv := Groupoid.inv

end End

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.isUnit_iff_isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isUnit_iff_isIso {C : Type u} [Category.{v} C] {X : C} (f : End X) : IsUni
t (f : End X) ↔ IsIso f
参数：f : End X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.inv_val`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), self.inv * 
↑self = 1
· 使用定理 `Units.val_inv`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), ↑self * sel
f.inv = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
-/
theorem isUnit_iff_isIso {C : Type u} [Category.{v} C] {X : C} (f : End X) :
    IsUnit (f : End X) ↔ IsIso f :=
  ⟨fun h => { out := ⟨h.unit.inv, ⟨h.unit.inv_val, h.unit.val_inv⟩⟩ }, fun h =>
    ⟨⟨f, inv f, by simp, by simp⟩, rfl⟩⟩

variable {C : Type u} [Category.{v} C] (X : C)

/-- Automorphisms of an object in a category.

The order of arguments in multiplication agrees with
`Function.comp`, not with `CategoryTheory.CategoryStruct.comp`.
-/
/-
**CategoryTheory.Aut** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Aut (X : C)
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Automorphisms of an object in a category.

The order of arguments in multiplication agrees with
`Function.comp`, not with `CategoryTheory.CategoryStruct.comp`.
-/
def Aut (X : C) := X ≅ X

namespace Aut

@[ext]
/-
**CategoryTheory.Aut.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Aut`。
形式化陈述：ext {X : C} {φ₁ φ₂ : Aut X} (h : φ₁.hom = φ₂.hom) : φ₁ = φ₂
参数：h : φ₁.hom = φ₂.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
-/
lemma ext {X : C} {φ₁ φ₂ : Aut X} (h : φ₁.hom = φ₂.hom) : φ₁ = φ₂ :=
  Iso.ext h
/-
**CategoryTheory.Aut.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Aut`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → (X : C) → Inhab
ited (CategoryTheory.Aut X)
参数：X : C；CategoryTheory.Aut X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance inhabited : Inhabited (Aut X) := ⟨Iso.refl X⟩
/-
**CategoryTheory.Aut.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Aut`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (Aut X) where
  one := Iso.refl X
  inv := Iso.symm
  mul x y := Iso.trans y x
  mul_assoc _ _ _ := (Iso.trans_assoc _ _ _).symm
  one_mul := Iso.trans_refl
  mul_one := Iso.refl_trans
  inv_mul_cancel := Iso.self_symm_id
/-
**CategoryTheory.Aut.Aut_mul_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Aut`。
形式化陈述：Aut_mul_def (f g : Aut X) : f * g = g.trans f
参数：f g : Aut X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Aut_mul_def (f g : Aut X) : f * g = g.trans f := rfl
/-
**CategoryTheory.Aut.Aut_inv_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Aut`。
形式化陈述：Aut_inv_def (f : Aut X) : f⁻¹ = f.symm
参数：f : Aut X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Aut_inv_def (f : Aut X) : f⁻¹ = f.symm := rfl

/-- Units in the monoid of endomorphisms of an object
are (multiplicatively) equivalent to automorphisms of that object.
-/
/-
**CategoryTheory.Aut.unitsEndEquivAut** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Aut`。
形式化陈述：unitsEndEquivAut : (End X)ˣ ≃* Aut X where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …

--- 原说明 ---
Units in the monoid of endomorphisms of an object
are (multiplicatively) equivalent to automorphisms of that object.
-/
def unitsEndEquivAut : (End X)ˣ ≃* Aut X where
  toFun f := ⟨f.1, f.2, f.4, f.3⟩
  invFun f := ⟨f.1, f.2, f.4, f.3⟩
  map_mul' f g := by cases f; cases g; rfl

/-- The inclusion of `Aut X` to `End X` as a monoid homomorphism. -/
@[simps!]
/-
**CategoryTheory.Aut.toEnd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Aut`。
形式化陈述：toEnd (X : C) : Aut X ->* End X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of `Aut X` to `End X` as a monoid homomorphism.
-/
def toEnd (X : C) : Aut X →* End X := (Units.coeHom (End X)).comp (Aut.unitsEndEquivAut X).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Isomorphisms induce isomorphisms of the automorphism group -/
/-
**CategoryTheory.Aut.autMulEquivOfIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Aut`。
形式化陈述：autMulEquivOfIso {X Y : C} (h : X ≅ Y) : Aut X ≃* Aut Y where toFun x
参数：h : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphisms induce isomorphisms of the automorphism group
-/
def autMulEquivOfIso {X Y : C} (h : X ≅ Y) : Aut X ≃* Aut Y where
  toFun x := { hom := h.inv ≫ x.hom ≫ h.hom, inv := h.inv ≫ x.inv ≫ h.hom }
  invFun y := { hom := h.hom ≫ y.hom ≫ h.inv, inv := h.hom ≫ y.inv ≫ h.inv }
  left_inv _ := by cat_disch
  right_inv _ := by cat_disch
  map_mul' := by simp [Aut_mul_def]

end Aut

namespace Functor

variable {D : Type u'} [Category.{v'} D] (f : C ⥤ D)

/-- `f.map` as a monoid hom between endomorphism monoids. -/
@[simps]
/-
**CategoryTheory.Functor.mapEnd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：mapEnd : End X ->* End (f.obj X) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…

--- 原说明 ---
`f.map` as a monoid hom between endomorphism monoids.
-/
def mapEnd : End X →* End (f.obj X) where
  toFun := f.map
  map_mul' x y := f.map_comp y x
  map_one' := f.map_id X

/-- `f.mapIso` as a group hom between automorphism groups. -/
/-
**CategoryTheory.Functor.mapAut** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：mapAut : Aut X ->* Aut (f.obj X) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mapIso_refl`：mapIso_refl (F : C ⥤ D) (X : C) : F.
mapIso (Iso.refl X) = Iso.refl (F.obj X)
· 使用定理 `CategoryTheory.Functor.mapIso_trans`：mapIso_trans (F : C ⥤ D) {X Y Z : C
} (i : X ≅ Y) (j : Y ≅ Z) : F.mapIso (i ≪≫ j) = F.mapIso i ≪≫ F.mapIso j

--- 原说明 ---
`f.mapIso` as a group hom between automorphism groups.
-/
def mapAut : Aut X →* Aut (f.obj X) where
  toFun := f.mapIso
  map_mul' x y := f.mapIso_trans y x
  map_one' := f.mapIso_refl X

namespace FullyFaithful

variable {f}
variable (hf : FullyFaithful f)

/-- `mulEquivEnd` as an isomorphism between endomorphism monoids. -/
@[simps!]
/-
**CategoryTheory.Functor.FullyFaithful.mulEquivEnd** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor.FullyFaithful`。
形式化陈述：mulEquivEnd (X : C) : End X ≃* End (f.obj X) where toEquiv
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mulEquivEnd` as an isomorphism between endomorphism monoids.
-/
noncomputable def mulEquivEnd (X : C) :
    End X ≃* End (f.obj X) where
  toEquiv := hf.homEquiv
  __ := mapEnd X f

/-- `mulEquivAut` as an isomorphism between automorphism groups. -/
@[simps!]
/-
**CategoryTheory.Functor.FullyFaithful.autMulEquivOfFullyFaithful** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Functor.FullyFaithful`。
形式化陈述：autMulEquivOfFullyFaithful (X : C) : Aut X ≃* Aut (f.obj X) where toEquiv
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mulEquivAut` as an isomorphism between automorphism groups.
-/
noncomputable def autMulEquivOfFullyFaithful (X : C) :
    Aut X ≃* Aut (f.obj X) where
  toEquiv := hf.isoEquiv
  __ := mapAut X f

end FullyFaithful

end Functor

/-- The multiplicative bijection `End X ≃* End (F X)` when `X : InducedCategory C F`. -/
@[simps!]
/-
**CategoryTheory.InducedCategory.endEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.InducedCategory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       {F : D → C} → {X : CategoryTheory.InducedCategory C F} → CategoryT
heory.End X ≃* CategoryTheory.End (F X)
参数：F X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative bijection `End X ≃* End (F X)` when `X : InducedCategory C F`
.
-/
def InducedCategory.endEquiv {D : Type*} {F : D → C}
    {X : InducedCategory C F} : End X ≃* End (F X) where
  toEquiv := InducedCategory.homEquiv
  map_mul' _ _ := rfl

end CategoryTheory

