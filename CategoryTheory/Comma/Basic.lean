/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Products.Unitor

/-!
# Comma categories

A comma category is a construction in category theory, which builds a category out of two functors
with a common codomain. Specifically, for functors `L : A ⥤ T` and `R : B ⥤ T`, an object in
`Comma L R` is a morphism `hom : L.obj left ⟶ R.obj right` for some objects `left : A` and
`right : B`, and a morphism in `Comma L R` between `hom : L.obj left ⟶ R.obj right` and
`hom' : L.obj left' ⟶ R.obj right'` is a commutative square

```
L.obj left  ⟶  L.obj left'
      |               |
  hom |               | hom'
      ↓               ↓
R.obj right ⟶  R.obj right',
```

where the top and bottom morphism come from morphisms `left ⟶ left'` and `right ⟶ right'`,
respectively.

## Main definitions

* `Comma L R`: the comma category of the functors `L` and `R`.
* `Over X`: the over category of the object `X` (developed in `Over.lean`).
* `Under X`: the under category of the object `X` (also developed in `Over.lean`).
* `Arrow T`: the arrow category of the category `T` (developed in `Arrow.lean`).

## References

* <https://ncatlab.org/nlab/show/comma+category>

## Tags

comma, slice, coslice, over, under, arrow
-/

@[expose] public section

namespace CategoryTheory

open Category

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable {A' : Type u₄} [Category.{v₄} A']
variable {B' : Type u₅} [Category.{v₅} B']
variable {T' : Type u₆} [Category.{v₆} T']

to_dual_name_hint Left Right, Fst Snd, L R, L₁ R₁, L₂ R₂, A B, F₁ F₂

set_option linter.translate.warnInvalid false in
/-- The objects of the comma category are triples of an object `left : A`, an object
`right : B` and a morphism `hom : L.obj left ⟶ R.obj right`. -/
@[to_dual self (reorder := A B, 2 4, L R), wikidata Q1780005]
/-
**CategoryTheory.Comma** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{A : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} A] →     {B : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} B] →         {T : Typ
e u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} T] →             Ca
tegoryTheory.Functor A T → CategoryTheory.Functor B T → Type (max u₁ u₂ v₃)
参数：max u₁ u₂ v₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The objects of the comma category are triples of an object `left : A`, an object
`right : B` and a morphism `hom : L.obj left ⟶ R.obj right`.
-/
structure Comma (L : A ⥤ T) (R : B ⥤ T) : Type max u₁ u₂ v₃ where
  /-- The left subobject -/
  left : A
  /-- The right subobject -/
  right : B
  /-- A morphism from `L.obj left` to `R.obj right` -/
  hom : L.obj left ⟶ R.obj right

attribute [to_dual existing] Comma.left
attribute [to_dual self] Comma.hom Comma.mk

-- Satisfying the inhabited linter
/-
**CategoryTheory.Comma.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma
`。
形式化陈述：{T : Type u₃} →   [inst : CategoryTheory.Category.{v₃, u₃} T] →     [Inhab
ited T] → Inhabited (CategoryTheory.Comma (CategoryTheory.Functor.id T) (Categor
yTheory.Functor.id T))
参数：CategoryTheory.Comma (CategoryTheory.Functor.id T) (CategoryTheory.Functor.id
 T)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Comma.inhabited [Inhabited T] : Inhabited (Comma (𝟭 T) (𝟭 T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 default }

variable {L : A ⥤ T} {R : B ⥤ T}

set_option linter.translate.warnInvalid false in
/-- A morphism between two objects in the comma category is a commutative square connecting the
morphisms coming from the two objects using morphisms in the image of the functors `L` and `R`.
-/
@[ext, to_dual self (reorder := A B, 2 4, L R, X Y)]
/-
**CategoryTheory.CommaMorphism** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：CommaMorphism (X Y : Comma L R) where /-- Morphism on left objects -/ left
 : X.left ⟶ Y.left /-- Morphism on right objects -/ right : X.right ⟶ Y.right w 
: L.map left ≫ Y.hom = X.hom ≫ R.map right
参数：X Y : Comma L R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism between two objects in the comma category is a commutative square con
necting the
morphisms coming from the two objects using morphisms in the image of the functo
rs `L` and `R`.
-/
structure CommaMorphism (X Y : Comma L R) where
  /-- Morphism on left objects -/
  left : X.left ⟶ Y.left
  /-- Morphism on right objects -/
  right : X.right ⟶ Y.right
  w : L.map left ≫ Y.hom = X.hom ≫ R.map right := by cat_disch

attribute [to_dual existing] CommaMorphism.left

@[to_dual existing w]
/-
**CategoryTheory.CommaMorphism.w'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comm
aMorphism`。
形式化陈述：∀ {A : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} A] {B : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} B]   {T : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} T] {L : CategoryTheory.Functor A T}   {R : CategoryTheo
ry.Functor B T} {X Y : CategoryTheory.Comma R L} (self : CategoryTheory.CommaMor
phism Y X),   CategoryTheory.CategoryStruct.comp Y.hom (L.map self.right) =     
CategoryTheory.CategoryStruct.comp (R.map self.left) X.hom
参数：self : CategoryTheory.CommaMorphism Y X；L.map self.right；R.map self.left。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
-/
theorem CommaMorphism.w' {X Y : Comma R L} (self : CommaMorphism Y X) :
    Y.hom ≫ L.map self.right = R.map self.left ≫ X.hom :=
  self.w.symm

/-- `CommaMorphism.mk'` is the dual of `CommaMorphism.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk]
/-
**CategoryTheory.CommaMorphism.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Com
maMorphism`。
形式化陈述：{A : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} A] →     {B : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} B] →         {T : Typ
e u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} T] →             {L
 : CategoryTheory.Functor A T} →               {R : CategoryTheory.Functor B T} 
→                 {X Y : CategoryTheory.Comma R L} →                   (right : 
Y.right ⟶ X.right) →                     (left : Y.left ⟶ X.left) →             
          CategoryTheory.CategoryStruct.comp Y.hom (L.map right) =              
             CategoryTheory.CategoryStruct.comp (R.map left) X.hom →            
             CategoryTheory.CommaMorphism Y X
参数：right : Y.right ⟶ X.right；left : Y.left ⟶ X.left；L.map right；R.map left。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CommaMorphism.mk'` is the dual of `CommaMorphism.mk`, which we need for `to_dua
l`.
Please avoid using this directly.
-/
abbrev CommaMorphism.mk' {X Y : Comma R L}
    (right : Y.right ⟶ X.right) (left : Y.left ⟶ X.left)
    (w : Y.hom ≫ L.map right = R.map left ≫ X.hom) :
    CommaMorphism Y X where
  left; right; w := w.symm

-- Satisfying the inhabited linter
/-
**CategoryTheory.CommaMorphism.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.CommaMorphism`。
形式化陈述：{A : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} A] →     {B : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} B] →         {T : Typ
e u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} T] →             {L
 : CategoryTheory.Functor A T} →               {R : CategoryTheory.Functor B T} 
→                 [inst_3 : Inhabited (CategoryTheory.Comma L R)] →             
      Inhabited (CategoryTheory.CommaMorphism default default)
参数：CategoryTheory.Comma L R；CategoryTheory.CommaMorphism default default。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance CommaMorphism.inhabited [Inhabited (Comma L R)] :
    Inhabited (CommaMorphism (default : Comma L R) default) :=
    ⟨{ left := 𝟙 _, right := 𝟙 _}⟩

attribute [reassoc (attr := simp)] CommaMorphism.w

@[to_dual self]
/-
**CategoryTheory.commaCategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：commaCategory : Category (Comma L R) where Hom X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commaCategory : Category (Comma L R) where
  Hom X Y := CommaMorphism X Y
  id X :=
    { left := 𝟙 X.left
      right := 𝟙 X.right }
  comp f g :=
    { left := f.left ≫ g.left
      right := f.right ≫ g.right }

namespace Comma

section

variable {X Y Z : Comma L R} {f : X ⟶ Y} {g : Y ⟶ Z}

@[ext, to_dual self (reorder := A B, 2 4, L R, X Y, h₁ h₂)]
/-
**CategoryTheory.Comma.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) : f 
= g
参数：f g : X ⟶ Y；h₁ : f.left = g.left；h₂ : f.right = g.right。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommaMorphism.ext`：∀ {A : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} A} {B : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} B
}   {T : Type u₃} {ins…
-/
lemma hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) : f = g :=
  CommaMorphism.ext h₁ h₂

@[to_dual (attr := simp)]
/-
**CategoryTheory.Comma.id_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：id_left : (𝟙 X : CommaMorphism X X).left = 𝟙 X.left
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_left : (𝟙 X : CommaMorphism X X).left = 𝟙 X.left :=
  rfl

@[to_dual (attr := simp)]
/-
**CategoryTheory.Comma.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comma
`。
形式化陈述：comp_left : (f ≫ g).left = f.left ≫ g.left
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_left : (f ≫ g).left = f.left ≫ g.left :=
  rfl

end

variable (L) (R)

set_option linter.translate.warnInvalid false in
/-- The functor sending an object `X` in the comma category to `X.left`. -/
@[to_dual (reorder := L R) (attr := simps, implicit_reducible)
/-- The functor sending an object `X` in the comma category to `X.right`. -/]
/-
**CategoryTheory.Comma.fst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：fst : Comma L R ⥤ A where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fst : Comma L R ⥤ A where
  obj X := X.left
  map f := f.left

attribute [to_dual existing] fst_map

set_option backward.defeqAttrib.useBackward true in
/-- We can interpret the commutative square constituting a morphism in the comma category as a
natural transformation between the functors `fst ⋙ L` and `snd ⋙ R` from the comma category
to `T`, where the components are given by the morphism that constitutes an object of the comma
category. -/
@[simps, to_dual self]
/-
**CategoryTheory.Comma.natTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma`
。
形式化陈述：natTrans : fst L R ⋙ L ⟶ snd L R ⋙ R where app X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can interpret the commutative square constituting a morphism in the comma cat
egory as a
natural transformation between the functors `fst ⋙ L` and `snd ⋙ R` from the com
ma category
to `T`, where the components are given by the morphism that constitutes an objec
t of the comma
category.
-/
def natTrans : fst L R ⋙ L ⟶ snd L R ⋙ R where app X := X.hom

@[simp]
/-
**CategoryTheory.Comma.eqToHom_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Co
mma`。
形式化陈述：eqToHom_left (X Y : Comma L R) (H : X = Y) : CommaMorphism.left (eqToHom H
) = eqToHom (by cases H; rfl)
参数：X Y : Comma L R；H : X = Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem eqToHom_left (X Y : Comma L R) (H : X = Y) :
    CommaMorphism.left (eqToHom H) = eqToHom (by cases H; rfl) := by
  cases H
  rfl

@[simp]
/-
**CategoryTheory.Comma.eqToHom_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
omma`。
形式化陈述：eqToHom_right (X Y : Comma L R) (H : X = Y) : CommaMorphism.right (eqToHom
 H) = eqToHom (by cases H; rfl)
参数：X Y : Comma L R；H : X = Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem eqToHom_right (X Y : Comma L R) (H : X = Y) :
    CommaMorphism.right (eqToHom H) = eqToHom (by cases H; rfl) := by
  cases H
  rfl

section

variable {L R} {X Y : Comma L R} (e : X ⟶ Y)

@[to_dual]
/-
**CategoryTheory.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIso e] : IsIso e.left :=
  (Comma.fst L R).map_isIso e

@[to_dual (attr := simp, push ←)]
/-
**CategoryTheory.Comma.inv_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Comma`
。
形式化陈述：inv_left [IsIso e] : (inv e).left = inv e.left
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_hom_inv_id`：eq_inv_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : g = inv f
· 使用定理 `CategoryTheory.Comma.instIsIsoLeft`：∀ {A : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 B]   {T : Type u₃} [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Comma.comp_left`：comp_left : (f ≫ g).left = f.left ≫ g.le
ft
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Comma.id_left`：id_left : (𝟙 X : CommaMorphism X X).left =
 𝟙 X.left
-/
lemma inv_left [IsIso e] : (inv e).left = inv e.left := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← Comma.comp_left, IsIso.hom_inv_id, id_left]

@[to_dual inv_left_hom_right]
/-
**CategoryTheory.Comma.left_hom_inv_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Comma`。
形式化陈述：left_hom_inv_right [IsIso e] : L.map (e.left) ≫ Y.hom ≫ R.map (inv e.right
) = X.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Comma.instIsIsoRight`：∀ {B : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} B] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} A]   {T : Type u₃} [ins…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.CommaMorphism.w_assoc`：∀ {A : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} B]   {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma left_hom_inv_right [IsIso e] : L.map (e.left) ≫ Y.hom ≫ R.map (inv e.right) = X.hom := by
  simp

end

section

variable {L₁ L₂ L₃ : A ⥤ T} {R₁ R₂ R₃ : B ⥤ T}

set_option linter.translate.warnInvalid false in
/-- Extract the isomorphism between the left objects from an isomorphism in the comma category. -/
@[to_dual (attr := simps!)
/-- Extract the isomorphism between the right objects from an isomorphism in the comma category. -/]
/-
**CategoryTheory.Comma.leftIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：leftIso {X Y : Comma L₁ R₁} (α : X ≅ Y) : X.left ≅ Y.left
参数：α : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def leftIso {X Y : Comma L₁ R₁} (α : X ≅ Y) : X.left ≅ Y.left := (fst L₁ R₁).mapIso α

attribute [to_dual existing rightIso_inv] leftIso_hom
attribute [to_dual existing rightIso_hom] leftIso_inv

/-- Construct an isomorphism in the comma category given isomorphisms of the objects whose forward
directions give a commutative square.
-/
@[to_dual none, simps (attr := to_dual none)]
/-
**CategoryTheory.Comma.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：isoMk {X Y : Comma L₁ R₁} (l : X.left ≅ Y.left) (r : X.right ≅ Y.right) (h
 : L₁.map l.hom ≫ Y.hom = X.hom ≫ R₁.map r.hom
参数：l : X.left ≅ Y.left；r : X.right ≅ Y.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism in the comma category given isomorphisms of the objects
 whose forward
directions give a commutative square.
-/
def isoMk {X Y : Comma L₁ R₁} (l : X.left ≅ Y.left) (r : X.right ≅ Y.right)
    (h : L₁.map l.hom ≫ Y.hom = X.hom ≫ R₁.map r.hom := by cat_disch) : X ≅ Y where
  hom :=
    { left := l.hom
      right := r.hom
      w := h }
  inv :=
    { left := l.inv
      right := r.inv
      w := by
        rw [← L₁.mapIso_inv l, Iso.inv_comp_eq, L₁.mapIso_hom, ← Category.assoc, h,
          Category.assoc, ← R₁.map_comp]
        simp }

section

variable {L R}
variable {L' : A' ⥤ T'} {R' : B' ⥤ T'}
  {F₁ : A ⥤ A'} {F₂ : B ⥤ B'} {F : T ⥤ T'}
  (α : F₁ ⋙ L' ⟶ L ⋙ F) (β : R ⋙ F ⟶ F₂ ⋙ R')

/-- The functor `Comma L R ⥤ Comma L' R'` induced by three functors `F₁`, `F₂`, `F`
and two natural transformations `F₁ ⋙ L' ⟶ L ⋙ F` and `R ⋙ F ⟶ F₂ ⋙ R'`. -/
@[simps, implicit_reducible,
  to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β)]
/-
**CategoryTheory.Comma.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：map : Comma L R ⥤ Comma L' R' where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map : Comma L R ⥤ Comma L' R' where
  obj X :=
    { left := F₁.obj X.left
      right := F₂.obj X.right
      hom := α.app X.left ≫ F.map X.hom ≫ β.app X.right }
  map {X Y} φ :=
    { left := F₁.map φ.left
      right := F₂.map φ.right
      w := by
        dsimp
        rw [assoc, assoc, ← Functor.comp_map, α.naturality_assoc, ← Functor.comp_map,
          ← β.naturality]
        dsimp
        rw [← F.map_comp_assoc, ← F.map_comp_assoc, φ.w] }

attribute [to_dual existing] map_obj_left
attribute [to_dual existing (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, X Y)]
  map_map_left

@[to_dual existing (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β) map_obj_hom]
/-
**CategoryTheory.Comma.map_obj_hom'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Co
mma`。
形式化陈述：map_obj_hom' (X : Comma L R) : ((map α β).obj X).hom = (α.app X.left ≫ F.m
ap X.hom) ≫ β.app X.right
参数：X : Comma L R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_obj_hom' (X : Comma L R) :
    ((map α β).obj X).hom = (α.app X.left ≫ F.map X.hom) ≫ β.app X.right := by simp

@[to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, 22 23)]
/-
**CategoryTheory.Comma.faithful_map** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
mma`。
形式化陈述：faithful_map [F₁.Faithful] [F₂.Faithful] : (map α β).Faithful where map_in
jective {X Y} f g h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Comma.hom_ext`：hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.lef
t) (h₂ : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance faithful_map [F₁.Faithful] [F₂.Faithful] : (map α β).Faithful where
  map_injective {X Y} f g h := by
    ext
    · exact F₁.map_injective (congr_arg CommaMorphism.left h)
    · exact F₂.map_injective (congr_arg CommaMorphism.right h)

@[to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, 23 24, 25 26)]
/-
**CategoryTheory.Comma.full_map** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comma`
。
形式化陈述：full_map [F.Faithful] [F₁.Full] [F₂.Full] [IsIso α] [IsIso β] : (map α β).
Full where map_surjective {X Y} φ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Comma.hom_ext`：hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.lef
t) (h₂ : f.right = g.right) : f = g
-/
instance full_map [F.Faithful] [F₁.Full] [F₂.Full] [IsIso α] [IsIso β] : (map α β).Full where
  map_surjective {X Y} φ :=
    ⟨{left := F₁.preimage φ.left
      right := F₂.preimage φ.right
      w := F.map_injective (by
        rw [← cancel_mono (β.app _), ← cancel_epi (α.app _), F.map_comp, F.map_comp, assoc, assoc]
        calc
        _ = (F₁ ⋙ L').map (F₁.preimage φ.left) ≫ α.app Y.left ≫ F.map Y.hom ≫ β.app Y.right := by
          rw [← Functor.comp_map, ← α.naturality_assoc]
        _ = α.app X.left ≫ F.map X.hom ≫ β.app X.right ≫ (F₂ ⋙ R').map (F₂.preimage φ.right) := by
          simp only [Functor.comp_map, Functor.map_preimage, ← map_obj_hom α β Y, φ.w,
            map_obj_hom α β X, assoc]
        _ = _ := by rw [← Functor.comp_map, β.naturality] )},
      by cat_disch⟩

set_option backward.defeqAttrib.useBackward true in
@[to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, 22 23, 25 26)]
/-
**CategoryTheory.Comma.essSurj_map** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Com
ma`。
形式化陈述：essSurj_map [F₁.EssSurj] [F₂.EssSurj] [F.Full] [IsIso α] [IsIso β] : (map 
α β).EssSurj where mem_essImage X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.preimage.congr_simp`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {X Y : C} (F : Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
instance essSurj_map [F₁.EssSurj] [F₂.EssSurj] [F.Full] [IsIso α] [IsIso β] :
    (map α β).EssSurj where
  mem_essImage X :=
    ⟨{left := F₁.objPreimage X.left
      right := F₂.objPreimage X.right
      hom := F.preimage ((inv α).app _ ≫ L'.map (F₁.objObjPreimageIso X.left).hom ≫
        X.hom ≫ R'.map (F₂.objObjPreimageIso X.right).inv ≫ (inv β).app _) },
          ⟨isoMk (F₁.objObjPreimageIso X.left) (F₂.objObjPreimageIso X.right) (by
            dsimp
            simp only [NatIso.isIso_inv_app, Functor.comp_obj, Functor.map_preimage, assoc,
              IsIso.inv_hom_id, comp_id, IsIso.hom_inv_id_assoc]
            rw [← R'.map_comp, Iso.inv_hom_id, R'.map_id, comp_id])⟩⟩

@[to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, 22 23, 26 27)]
/-
**CategoryTheory.Comma.isEquivalenceMap** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Comma`。
形式化陈述：∀ {A : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} A] {B : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} B]   {T : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} T] {A' : Type u₄}   [inst_3 : CategoryTheory.Category.{
v₄, u₄} A'] {B' : Type u₅} [inst_4 : CategoryTheory.Category.{v₅, u₅} B']   {T' 
: Type u₆} [inst_5 : CategoryTheory.Category.{v₆, u₆} T'] {L : CategoryTheory.Fu
nctor A T}   {R : CategoryTheory.Functor B T} {L' : CategoryTheory.Functor A' T'
} {R' : CategoryTheory.Functor B' T'}   {F₁ : CategoryTheory.Functor A A'} {F₂ :
 CategoryTheory.Functor B B'} {F : CategoryTheory.Functor T T'}   (α : F₁.comp L
' ⟶ L.comp F) (β : R.comp F ⟶ F₂.comp R') [F₁.IsEquivalence] [F₂.IsEquivalence] 
[F.Faithful] [F.Full]   [CategoryTheory.IsIso α] [CategoryTheory.IsIso β], (Cate
goryTheory.Comma.map α β).IsEquivalence
参数：α : F₁.comp L' ⟶ L.comp F；β : R.comp F ⟶ F₂.comp R'；CategoryTheory.Comma.map 
α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…
-/
noncomputable instance isEquivalenceMap
    [F₁.IsEquivalence] [F₂.IsEquivalence] [F.Faithful] [F.Full] [IsIso α] [IsIso β] :
    (map α β).IsEquivalence where

/-- The equality between `map α β ⋙ fst L' R'` and `fst L R ⋙ F₁`,
where `α : F₁ ⋙ L' ⟶ L ⋙ F`. -/
@[to_dual (attr := simp) (reorder := α β)
/-- The equality between `map α β ⋙ snd L' R'` and `snd L R ⋙ F₂`,
where `β : R ⋙ F ⟶ F₂ ⋙ R'`. -/]
/-
**CategoryTheory.Comma.map_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：map_fst : map α β ⋙ fst L' R' = fst L R ⋙ F₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_fst : map α β ⋙ fst L' R' = fst L R ⋙ F₁ :=
  rfl

set_option linter.translate.warnInvalid false in
/-- The isomorphism between `map α β ⋙ fst L' R'` and `fst L R ⋙ F₁`,
where `α : F₁ ⋙ L' ⟶ L ⋙ F`. -/
@[to_dual (attr := simps!) (reorder := α β)
/-- The isomorphism between `map α β ⋙ snd L' R'` and `snd L R ⋙ F₂`,
where `β : R ⋙ F ⟶ F₂ ⋙ R'`. -/]
/-
**CategoryTheory.Comma.mapFst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：mapFst : map α β ⋙ fst L' R' ≅ fst L R ⋙ F₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapFst : map α β ⋙ fst L' R' ≅ fst L R ⋙ F₁ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by simp)

end

set_option linter.translate.warnInvalid false in
/-- A natural transformation `L₁ ⟶ L₂` induces a functor `Comma L₂ R ⥤ Comma L₁ R`. -/
@[to_dual (attr := simps, implicit_reducible)
/-- A natural transformation `R₁ ⟶ R₂` induces a functor `Comma L R₁ ⥤ Comma L R₂`. -/]
/-
**CategoryTheory.Comma.mapLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：mapLeft (l : L₁ ⟶ L₂) : Comma L₂ R ⥤ Comma L₁ R where obj X
参数：l : L₁ ⟶ L₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapLeft (l : L₁ ⟶ L₂) : Comma L₂ R ⥤ Comma L₁ R where
  obj X :=
    { left := X.left
      right := X.right
      hom := l.app X.left ≫ X.hom }
  map f :=
    { left := f.left
      right := f.right }

attribute [to_dual existing] mapLeft_map_left
attribute [to_dual existing] mapLeft_map_right

set_option linter.translate.warnInvalid false in
/-- The functor `Comma L R ⥤ Comma L R` induced by the identity natural transformation on `L` is
naturally isomorphic to the identity functor. -/
@[to_dual (attr := simps!)
/-- The functor `Comma L R ⥤ Comma L R` induced by the identity natural transformation on `R` is
naturally isomorphic to the identity functor. -/]
/-
**CategoryTheory.Comma.mapLeftId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma
`。
形式化陈述：mapLeftId : mapLeft R (𝟙 L) ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapLeftId : mapLeft R (𝟙 L) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option linter.translate.warnInvalid false in
/-- The functor `Comma L₁ R ⥤ Comma L₃ R` induced by the composition of two natural transformations
`l : L₁ ⟶ L₂` and `l' : L₂ ⟶ L₃` is naturally isomorphic to the composition of the two functors
induced by these natural transformations. -/
@[to_dual (attr := simps!)
/-- The functor `Comma L R₁ ⥤ Comma L R₃` induced by the composition of the natural transformations
`r : R₁ ⟶ R₂` and `r' : R₂ ⟶ R₃` is naturally isomorphic to the composition of the functors
induced by these natural transformations. -/]
/-
**CategoryTheory.Comma.mapLeftComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Com
ma`。
形式化陈述：mapLeftComp (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃) : mapLeft R (l ≫ l') ≅ mapLeft R 
l' ⋙ mapLeft R l
参数：l : L₁ ⟶ L₂；l' : L₂ ⟶ L₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapLeftComp (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃) :
    mapLeft R (l ≫ l') ≅ mapLeft R l' ⋙ mapLeft R l :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option linter.translate.warnInvalid false in
/-- Two equal natural transformations `L₁ ⟶ L₂` yield naturally isomorphic functors
`Comma L₁ R ⥤ Comma L₂ R`. -/
@[to_dual (attr := simps!)
/-- Two equal natural transformations `R₁ ⟶ R₂` yield naturally isomorphic functors
`Comma L R₁ ⥤ Comma L R₂`. -/]
/-
**CategoryTheory.Comma.mapLeftEq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma
`。
形式化陈述：mapLeftEq (l l' : L₁ ⟶ L₂) (h : l = l') : mapLeft R l ≅ mapLeft R l'
参数：l l' : L₁ ⟶ L₂；h : l = l'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapLeftEq (l l' : L₁ ⟶ L₂) (h : l = l') : mapLeft R l ≅ mapLeft R l' :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.defeqAttrib.useBackward true in
set_option linter.translate.warnInvalid false in
/-- A natural isomorphism `L₁ ≅ L₂` induces an equivalence of categories
`Comma L₁ R ≌ Comma L₂ R`. -/
@[to_dual (attr := simps!, implicit_reducible)
/-- A natural isomorphism `R₁ ≅ R₂` induces an equivalence of categories
`Comma L R₁ ≌ Comma L R₂`. -/]
/-
**CategoryTheory.Comma.mapLeftIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comm
a`。
形式化陈述：mapLeftIso (i : L₁ ≅ L₂) : Comma L₁ R ≌ Comma L₂ R where functor
参数：i : L₁ ≅ L₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapLeftIso (i : L₁ ≅ L₂) : Comma L₁ R ≌ Comma L₂ R where
  functor := mapLeft _ i.inv
  inverse := mapLeft _ i.hom
  unitIso := (mapLeftId _ _).symm ≪≫ mapLeftEq _ _ _ i.hom_inv_id.symm ≪≫ mapLeftComp _ _ _
  counitIso := (mapLeftComp _ _ _).symm ≪≫ mapLeftEq _ _ _ i.inv_hom_id ≪≫ mapLeftId _ _

end

section

variable {C : Type u₄} [Category.{v₄} C]

set_option linter.translate.warnInvalid false in
/-- The functor `(F ⋙ L, R) ⥤ (L, R)` -/
@[to_dual (attr := simps,
  implicit_reducible) (reorder := F L R) /-- The functor `(L, F ⋙ R) ⥤ (L, R)` -/]
/-
**CategoryTheory.Comma.preLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：preLeft (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) : Comma (F ⋙ L) R ⥤ Comma L R 
where obj X
参数：F : C ⥤ A；L : A ⥤ T；R : B ⥤ T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def preLeft (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) : Comma (F ⋙ L) R ⥤ Comma L R where
  obj X :=
    { left := F.obj X.left
      right := X.right
      hom := X.hom }
  map f :=
    { left := F.map f.left
      right := f.right
      w := by simpa using! f.w }

set_option backward.defeqAttrib.useBackward true in
/-- `Comma.preLeft` is a particular case of `Comma.map`,
but with better definitional properties. -/
@[to_dual (reorder := F L R)
/-- `Comma.preRight` is a particular case of `Comma.map`,
but with better definitional properties. -/]
/-
**CategoryTheory.Comma.preLeftIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comm
a`。
形式化陈述：preLeftIso (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) : preLeft F L R ≅ map (F ⋙ 
L).rightUnitor.inv (R.rightUnitor.hom ≫ R.leftUnitor.inv)
参数：F : C ⥤ A；L : A ⥤ T；R : B ⥤ T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def preLeftIso (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) :
    preLeft F L R ≅ map (F ⋙ L).rightUnitor.inv (R.rightUnitor.hom ≫ R.leftUnitor.inv) :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _) (by simp -implicitDefEqProofs))

@[to_dual]
/-
**CategoryTheory.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.Faithful] : (preLeft F L R).Faithful :=
  Functor.Faithful.of_iso (preLeftIso F L R).symm

@[to_dual]
/-
**CategoryTheory.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.Full] : (preLeft F L R).Full :=
  Functor.Full.of_iso (preLeftIso F L R).symm

@[to_dual]
/-
**CategoryTheory.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.EssSurj] : (preLeft F L R).EssSurj :=
  Functor.essSurj_of_iso (preLeftIso F L R).symm

/-- If `F` is an equivalence, then so is `preLeft F L R`. -/
@[to_dual /-- If `F` is an equivalence, then so is `preRight L F R`. -/]
/-
**CategoryTheory.Comma.isEquivalence_preLeft** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Comma`。
形式化陈述：∀ {A : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} A] {B : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} B]   {T : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} T] {C : Type u₄}   [inst_3 : CategoryTheory.Category.{v
₄, u₄} C] (F : CategoryTheory.Functor C A) (L : CategoryTheory.Functor A T)   (R
 : CategoryTheory.Functor B T) [F.IsEquivalence], (CategoryTheory.Comma.preLeft 
F L R).IsEquivalence
参数：F : CategoryTheory.Functor C A；L : CategoryTheory.Functor A T；R : CategoryThe
ory.Functor B T；CategoryTheory.Comma.preLeft F L R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comma.instFaithfulCompPreLeft`：∀ {A : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} B]   {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Comma.instFullCompPreLeft`：∀ {A : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} B]   {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Comma.instEssSurjCompPreLeft`：∀ {A : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} B]   {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F` is an equivalence, then so is `preLeft F L R`.
-/
instance isEquivalence_preLeft (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.IsEquivalence] :
    (preLeft F L R).IsEquivalence where

/-- The functor `(L, R) ⥤ (L ⋙ F, R ⋙ F)` -/
@[implicit_reducible, to_dual self, simps]
/-
**CategoryTheory.Comma.post** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：post (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) : Comma L R ⥤ Comma (L ⋙ F) (R ⋙ 
F) where obj X
参数：L : A ⥤ T；R : B ⥤ T；F : T ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `(L, R) ⥤ (L ⋙ F, R ⋙ F)`
-/
def post (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) : Comma L R ⥤ Comma (L ⋙ F) (R ⋙ F) where
  obj X :=
    { left := X.left
      right := X.right
      hom := F.map X.hom }
  map f :=
    { left := f.left
      right := f.right
      w := by simp only [Functor.comp_map, ← F.map_comp, f.w] }

attribute [to_dual existing] post_obj_left
attribute [to_dual self] post_obj_hom

/-- `Comma.post` is a particular case of `Comma.map`, but with better definitional properties. -/
@[to_dual self]
/-
**CategoryTheory.Comma.postIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：postIso (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) : post L R F ≅ map (F₁
参数：L : A ⥤ T；R : B ⥤ T；F : T ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Comma.post` is a particular case of `Comma.map`, but with better definitional p
roperties.
-/
def postIso (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) :
    post L R F ≅ map (F₁ := 𝟭 _) (F₂ := 𝟭 _) (L ⋙ F).leftUnitor.hom (R ⋙ F).leftUnitor.inv :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

@[to_dual self]
/-
**CategoryTheory.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) : (post L R F).Faithful :=
  Functor.Faithful.of_iso (postIso L R F).symm

@[to_dual self]
/-
**CategoryTheory.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) [F.Faithful] : (post L R F).Full :=
  Functor.Full.of_iso (postIso L R F).symm

@[to_dual self]
/-
**CategoryTheory.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) [F.Full] : (post L R F).EssSurj :=
  Functor.essSurj_of_iso (postIso L R F).symm

/-- If `F` is an equivalence, then so is `post L R F`. -/
@[to_dual self]
/-
**CategoryTheory.Comma.isEquivalence_post** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Comma`。
形式化陈述：∀ {A : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} A] {B : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} B]   {T : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} T] {C : Type u₄}   [inst_3 : CategoryTheory.Category.{v
₄, u₄} C] (L : CategoryTheory.Functor A T) (R : CategoryTheory.Functor B T)   (F
 : CategoryTheory.Functor T C) [F.IsEquivalence], (CategoryTheory.Comma.post L R
 F).IsEquivalence
参数：L : CategoryTheory.Functor A T；R : CategoryTheory.Functor B T；F : CategoryThe
ory.Functor T C；CategoryTheory.Comma.post L R F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comma.instFaithfulCompPost`：∀ {A : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} B]   {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Comma.instFullCompPostOfFaithful`：∀ {A : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} B]   {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Comma.instEssSurjCompPostOfFull`：∀ {A : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} B]   {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F` is an equivalence, then so is `post L R F`.
-/
instance isEquivalence_post (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) [F.IsEquivalence] :
    (post L R F).IsEquivalence where

/-- The canonical functor from the product of two categories to the comma category of their
respective functors into `Discrete PUnit`. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Comma.fromProd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma`
。
形式化陈述：fromProd (L : A ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit) : A × B ⥤ Comma
 L R where obj X
参数：L : A ⥤ Discrete PUnit；R : B ⥤ Discrete PUnit。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical functor from the product of two categories to the comma category o
f their
respective functors into `Discrete PUnit`.
-/
def fromProd (L : A ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit) :
    A × B ⥤ Comma L R where
  obj X :=
    { left := X.1
      right := X.2
      hom := Discrete.eqToHom rfl }
  map {X} {Y} f :=
    { left := f.1
      right := f.2 }

set_option backward.defeqAttrib.useBackward true in
/-- Taking the comma category of two functors into `Discrete PUnit` results in something
is equivalent to their product. -/
@[simps!]
/-
**CategoryTheory.Comma.equivProd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma
`。
形式化陈述：equivProd (L : A ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit) : Comma L R ≌ 
A × B where functor
参数：L : A ⥤ Discrete PUnit；R : B ⥤ Discrete PUnit。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the comma category of two functors into `Discrete PUnit` results in somet
hing
is equivalent to their product.
-/
def equivProd (L : A ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit) :
    Comma L R ≌ A × B where
  functor := (fst L R).prod' (snd L R)
  inverse := fromProd L R
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Taking the comma category of a functor into `A ⥤ Discrete PUnit` and the identity
`Discrete PUnit ⥤ Discrete PUnit` results in a category equivalent to `A`. -/
/-
**CategoryTheory.Comma.toPUnitIdEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Comma`。
形式化陈述：toPUnitIdEquiv (L : A ⥤ Discrete PUnit) (R : Discrete PUnit ⥤ Discrete PUn
it) : Comma L R ≌ A
参数：L : A ⥤ Discrete PUnit；R : Discrete PUnit ⥤ Discrete PUnit。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the comma category of a functor into `A ⥤ Discrete PUnit` and the identit
y
`Discrete PUnit ⥤ Discrete PUnit` results in a category equivalent to `A`.
-/
def toPUnitIdEquiv (L : A ⥤ Discrete PUnit) (R : Discrete PUnit ⥤ Discrete PUnit) :
    Comma L R ≌ A :=
  (equivProd L _).trans (prod.rightUnitorEquivalence A)

@[simp]
/-
**CategoryTheory.Comma.toPUnitIdEquiv_functor_iso** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Comma`。
形式化陈述：toPUnitIdEquiv_functor_iso {L : A ⥤ Discrete PUnit} {R : Discrete PUnit ⥤ 
Discrete PUnit} : (toPUnitIdEquiv L R).functor = fst L R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPUnitIdEquiv_functor_iso {L : A ⥤ Discrete PUnit}
    {R : Discrete PUnit ⥤ Discrete PUnit} :
    (toPUnitIdEquiv L R).functor = fst L R :=
  rfl

/-- Taking the comma category of the identity `Discrete PUnit ⥤ Discrete PUnit`
and a functor `B ⥤ Discrete PUnit` results in a category equivalent to `B`. -/
/-
**CategoryTheory.Comma.toIdPUnitEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Comma`。
形式化陈述：toIdPUnitEquiv (L : Discrete PUnit ⥤ Discrete PUnit) (R : B ⥤ Discrete PUn
it) : Comma L R ≌ B
参数：L : Discrete PUnit ⥤ Discrete PUnit；R : B ⥤ Discrete PUnit。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the comma category of the identity `Discrete PUnit ⥤ Discrete PUnit`
and a functor `B ⥤ Discrete PUnit` results in a category equivalent to `B`.
-/
def toIdPUnitEquiv (L : Discrete PUnit ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit) :
    Comma L R ≌ B :=
  (equivProd _ R).trans (prod.leftUnitorEquivalence B)

@[simp]
/-
**CategoryTheory.Comma.toIdPUnitEquiv_functor_iso** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Comma`。
形式化陈述：toIdPUnitEquiv_functor_iso {L : Discrete PUnit ⥤ Discrete PUnit} {R : B ⥤ 
Discrete PUnit} : (toIdPUnitEquiv L R).functor = snd L R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIdPUnitEquiv_functor_iso {L : Discrete PUnit ⥤ Discrete PUnit}
    {R : B ⥤ Discrete PUnit} :
    (toIdPUnitEquiv L R).functor = snd L R :=
  rfl

end

section Opposite

open Opposite

set_option backward.defeqAttrib.useBackward true in
/-- The canonical functor from `Comma L R` to `(Comma R.op L.op)ᵒᵖ`. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Comma.opFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma
`。
形式化陈述：opFunctor : Comma L R ⥤ (Comma R.op L.op)ᵒᵖ where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical functor from `Comma L R` to `(Comma R.op L.op)ᵒᵖ`.
-/
def opFunctor : Comma L R ⥤ (Comma R.op L.op)ᵒᵖ where
  obj X := ⟨op X.right, op X.left, op X.hom⟩
  map f := ⟨op f.right, op f.left, Quiver.Hom.unop_inj (by simp)⟩

/-- Composing the `leftOp` of `opFunctor L R` with `fst L.op R.op` is naturally isomorphic
to `snd L R`. -/
@[simps!]
/-
**CategoryTheory.Comma.opFunctorCompFst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Comma`。
形式化陈述：opFunctorCompFst : (opFunctor L R).leftOp ⋙ fst _ _ ≅ (snd _ _).op
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing the `leftOp` of `opFunctor L R` with `fst L.op R.op` is naturally isom
orphic
to `snd L R`.
-/
def opFunctorCompFst : (opFunctor L R).leftOp ⋙ fst _ _ ≅ (snd _ _).op :=
  Iso.refl _

/-- Composing the `leftOp` of `opFunctor L R` with `snd L.op R.op` is naturally isomorphic
to `fst L R`. -/
@[simps!]
/-
**CategoryTheory.Comma.opFunctorCompSnd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Comma`。
形式化陈述：opFunctorCompSnd : (opFunctor L R).leftOp ⋙ snd _ _ ≅ (fst _ _).op
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing the `leftOp` of `opFunctor L R` with `snd L.op R.op` is naturally isom
orphic
to `fst L R`.
-/
def opFunctorCompSnd : (opFunctor L R).leftOp ⋙ snd _ _ ≅ (fst _ _).op :=
  Iso.refl _

/-- The canonical functor from `Comma L.op R.op` to `(Comma R L)ᵒᵖ`. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Comma.unopFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Com
ma`。
形式化陈述：unopFunctor : Comma L.op R.op ⥤ (Comma R L)ᵒᵖ where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical functor from `Comma L.op R.op` to `(Comma R L)ᵒᵖ`.
-/
def unopFunctor : Comma L.op R.op ⥤ (Comma R L)ᵒᵖ where
  obj X := ⟨X.right.unop, X.left.unop, X.hom.unop⟩
  map f := ⟨f.right.unop, f.left.unop, Quiver.Hom.op_inj (by simpa using! f.w.symm)⟩

/-- Composing `unopFunctor L R` with `(fst L R).op` is isomorphic to `snd L.op R.op`. -/
@[simps!]
/-
**CategoryTheory.Comma.unopFunctorCompFst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Comma`。
形式化陈述：unopFunctorCompFst : unopFunctor L R ⋙ (fst _ _).op ≅ snd _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing `unopFunctor L R` with `(fst L R).op` is isomorphic to `snd L.op R.op`
.
-/
def unopFunctorCompFst : unopFunctor L R ⋙ (fst _ _).op ≅ snd _ _ :=
  Iso.refl _

/-- Composing `unopFunctor L R` with `(snd L R).op` is isomorphic to `fst L.op R.op`. -/
@[simps!]
/-
**CategoryTheory.Comma.unopFunctorCompSnd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Comma`。
形式化陈述：unopFunctorCompSnd : unopFunctor L R ⋙ (snd _ _).op ≅ fst _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing `unopFunctor L R` with `(snd L R).op` is isomorphic to `fst L.op R.op`
.
-/
def unopFunctorCompSnd : unopFunctor L R ⋙ (snd _ _).op ≅ fst _ _ :=
  Iso.refl _

/-- The canonical equivalence between `Comma L R` and `(Comma R.op L.op)ᵒᵖ`. -/
@[simps]
/-
**CategoryTheory.Comma.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：opEquiv : Comma L R ≌ (Comma R.op L.op)ᵒᵖ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical equivalence between `Comma L R` and `(Comma R.op L.op)ᵒᵖ`.
-/
def opEquiv : Comma L R ≌ (Comma R.op L.op)ᵒᵖ where
  functor := opFunctor L R
  inverse := (unopFunctor R L).leftOp
  unitIso := NatIso.ofComponents (fun X => Iso.refl _)
  counitIso := NatIso.ofComponents (fun X => Iso.refl _)

end Opposite

end Comma

end CategoryTheory

