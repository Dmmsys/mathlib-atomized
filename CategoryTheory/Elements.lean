/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# The category of elements

This file defines the category of elements, also known as (a special case of) the Grothendieck
construction.

Given a functor `F : C ⥤ Type`, an object of `F.Elements` is a pair `(X : C, x : F.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.

## Implementation notes

This construction is equivalent to a special case of a comma construction, so this is mostly just a
more convenient API. We prove the equivalence in
`CategoryTheory.CategoryOfElements.structuredArrowEquivalence`.

## References
* [Emily Riehl, *Category Theory in Context*, Section 2.4][riehl2017]
* <https://en.wikipedia.org/wiki/Category_of_elements>
* <https://ncatlab.org/nlab/show/category+of+elements>

## Tags
category of elements, Grothendieck construction, comma category
-/

@[expose] public section


namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C]

/-- The type of objects for the category of elements of a functor `F : C ⥤ Type`
is a pair `(X : C, x : F.obj X)`.
-/
/-
**CategoryTheory.Functor.Elements** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Functor C (Type w) → Type (max u w)
参数：Type w；max u w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of objects for the category of elements of a functor `F : C ⥤ Type`
is a pair `(X : C, x : F.obj X)`.
-/
def Functor.Elements (F : C ⥤ Type w) :=
  Σ c : C, F.obj c

/-- Constructor for the type `F.Elements` when `F` is a functor to types. -/
/-
**CategoryTheory.Functor.elementsMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → (F : Category
Theory.Functor C (Type w)) → (X : C) → F.obj X → F.Elements
参数：F : CategoryTheory.Functor C (Type w)；X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for the type `F.Elements` when `F` is a functor to types.
-/
abbrev Functor.elementsMk (F : C ⥤ Type w) (X : C) (x : F.obj X) : F.Elements := ⟨X, x⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.Elements.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor.Elements`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheo
ry.Functor C (Type w)} (x y : F.Elements)   (h₁ : x.fst = y.fst), (CategoryTheor
y.ConcreteCategory.hom (F.map (CategoryTheory.eqToHom h₁))) x.snd = y.snd → x = 
y
参数：Type w；x y : F.Elements；h₁ : x.fst = y.fst；CategoryTheory.ConcreteCategory.ho
m (F.map (CategoryTheory.eqToHom h₁))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma Functor.Elements.ext {F : C ⥤ Type w} (x y : F.Elements) (h₁ : x.fst = y.fst)
    (h₂ : F.map (eqToHom h₁) x.snd = y.snd) : x = y := by
  cases x
  cases y
  cases h₁
  simp_all

/-- The category structure on `F.Elements`, for `F : C ⥤ Type`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`. -/
/-
**CategoryTheory.categoryOfElements** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：categoryOfElements (F : C ⥤ Type w) : Category.{v} F.Elements where Hom p 
q
参数：F : C ⥤ Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category structure on `F.Elements`, for `F : C ⥤ Type`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` take
s `x` to `y`.
-/
instance categoryOfElements (F : C ⥤ Type w) : Category.{v} F.Elements where
  Hom p q := { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 }
  id p := ⟨𝟙 p.1, by simp⟩
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by simp [f.2, g.2]⟩

/-- Natural transformations are mapped to functors between categories of elements. -/
@[simps]
/-
**CategoryTheory.NatTrans.mapElements** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
NatTrans`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F G : Ca
tegoryTheory.Functor C (Type w)} → (F ⟶ G) → CategoryTheory.Functor F.Elements G
.Elements
参数：Type w；F ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Natural transformations are mapped to functors between categories of elements.
-/
def NatTrans.mapElements {F G : C ⥤ Type w} (φ : F ⟶ G) : F.Elements ⥤ G.Elements where
  obj := fun ⟨X, x⟩ ↦ ⟨_, φ.app X x⟩
  map {p q} := fun ⟨f, h⟩ ↦ ⟨f, by have hb := φ.naturality_apply f p.2; cat_disch⟩

/-- The functor mapping functors `C ⥤ Type w` to their category of elements -/
@[simps]
/-
**CategoryTheory.Functor.elementsFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.Functor (CategoryTheory.Functor C (Type w)) CategoryTheory.Cat
参数：CategoryTheory.Functor C (Type w)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor mapping functors `C ⥤ Type w` to their category of elements
-/
def Functor.elementsFunctor : (C ⥤ Type w) ⥤ Cat where
  obj F := Cat.of F.Elements
  map n := (NatTrans.mapElements n).toCatHom

namespace CategoryOfElements

/-- Constructor for morphisms in the category of elements of a functor to types. -/
@[simps]
/-
**CategoryTheory.CategoryOfElements.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.CategoryOfElements`。
形式化陈述：homMk {F : C ⥤ Type w} (x y : F.Elements) (f : x.1 ⟶ y.1) (hf : F.map f x.
snd = y.snd) : x ⟶ y
参数：x y : F.Elements；f : x.1 ⟶ y.1；hf : F.map f x.snd = y.snd。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in the category of elements of a functor to types.
-/
def homMk {F : C ⥤ Type w} (x y : F.Elements) (f : x.1 ⟶ y.1) (hf : F.map f x.snd = y.snd) :
    x ⟶ y :=
  ⟨f, hf⟩

@[ext]
/-
**CategoryTheory.CategoryOfElements.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.CategoryOfElements`。
形式化陈述：ext (F : C ⥤ Type w) {x y : F.Elements} (f g : x ⟶ y) (w : f.val = g.val) 
: f = g
参数：F : C ⥤ Type w；f g : x ⟶ y；w : f.val = g.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem ext (F : C ⥤ Type w) {x y : F.Elements} (f g : x ⟶ y) (w : f.val = g.val) : f = g :=
  Subtype.ext w

@[simp]
/-
**CategoryTheory.CategoryOfElements.comp_val** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.CategoryOfElements`。
形式化陈述：comp_val {F : C ⥤ Type w} {p q r : F.Elements} {f : p ⟶ q} {g : q ⟶ r} : (
f ≫ g).val = f.val ≫ g.val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_val {F : C ⥤ Type w} {p q r : F.Elements} {f : p ⟶ q} {g : q ⟶ r} :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl

@[simp]
/-
**CategoryTheory.CategoryOfElements.id_val** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.CategoryOfElements`。
形式化陈述：id_val {F : C ⥤ Type w} {p : F.Elements} : (𝟙 p : p ⟶ p).val = 𝟙 p.1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_val {F : C ⥤ Type w} {p : F.Elements} : (𝟙 p : p ⟶ p).val = 𝟙 p.1 :=
  rfl

@[simp]
/-
**CategoryTheory.CategoryOfElements.map_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.CategoryOfElements`。
形式化陈述：map_snd {F : C ⥤ Type w} {p q : F.Elements} (f : p ⟶ q) : (F.map f.val) p.
2 = q.2
参数：f : p ⟶ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem map_snd {F : C ⥤ Type w} {p q : F.Elements} (f : p ⟶ q) : (F.map f.val) p.2 = q.2 :=
  f.property

/-- Constructor for isomorphisms in the category of elements of a functor to types. -/
@[simps]
/-
**CategoryTheory.CategoryOfElements.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.CategoryOfElements`。
形式化陈述：isoMk {F : C ⥤ Type w} (x y : F.Elements) (e : x.1 ≅ y.1) (he : F.map e.ho
m x.snd = y.snd) : x ≅ y where hom
参数：x y : F.Elements；e : x.1 ≅ y.1；he : F.map e.hom x.snd = y.snd。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in the category of elements of a functor to types.
-/
def isoMk {F : C ⥤ Type w} (x y : F.Elements) (e : x.1 ≅ y.1)
    (he : F.map e.hom x.snd = y.snd) : x ≅ y where
  hom := homMk x y e.hom he
  inv := homMk y x e.inv (by rw [← he, Functor.map_hom_inv'_apply])
/-
**CategoryTheory.CategoryOfElements.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
ategoryOfElements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallySmall.{w} C] (F : C ⥤ Type w) : LocallySmall.{w} F.Elements where
  hom_small := by
    rintro ⟨X, _⟩ ⟨Y, y⟩
    exact small_of_injective (f := fun g ↦ g.val) (by cat_disch)

end CategoryOfElements

/-
**CategoryTheory.groupoidOfElements** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：groupoidOfElements {G : Type u} [Groupoid.{v} G] (F : G ⥤ Type w) : Groupo
id F.Elements where inv {p q} f
参数：F : G ⥤ Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance groupoidOfElements {G : Type u} [Groupoid.{v} G] (F : G ⥤ Type w) :
    Groupoid F.Elements where
  inv {p q} f :=
    ⟨Groupoid.inv f.val,
      calc
        F.map (Groupoid.inv f.val) q.2 = F.map (Groupoid.inv f.val) (F.map f.val p.2) := by rw [f.2]
        _ = (F.map f.val ≫ F.map (Groupoid.inv f.val)) p.2 := rfl
        _ = p.2 := by
          rw [← F.map_comp]
          simp
        ⟩
  inv_comp _ := by
    ext
    simp
  comp_inv _ := by
    ext
    simp

namespace CategoryOfElements

variable (F : C ⥤ Type w)

/-- The functor out of the category of elements which forgets the element. -/
@[simps]
/-
**CategoryTheory.CategoryOfElements.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.C
ategoryOfElements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor out of the category of elements which forgets the element.
-/
def π : F.Elements ⥤ C where
  obj X := X.1
  map f := f.val
/-
**CategoryTheory.CategoryOfElements.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
ategoryOfElements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (π F).Faithful where

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.CategoryOfElements.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
ategoryOfElements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (π F).ReflectsIsomorphisms where
  reflects f h := by
    refine ⟨⟨(inv ((π F).map f) :), ?_⟩, ?_, ?_⟩
    · simp only [← map_snd f, ← Functor.map_comp_apply,
        π_obj, π_map, IsIso.hom_inv_id, Functor.map_id_apply]
    · cat_disch
    · cat_disch

/-- A natural transformation between functors induces a functor between the categories of elements.
-/
@[simps]
/-
**CategoryTheory.CategoryOfElements.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.CategoryOfElements`。
形式化陈述：map {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : F₁.Elements ⥤ F₂.Elements where o
bj t
参数：α : F₁ ⟶ F₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation between functors induces a functor between the categori
es of elements.
-/
def map {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : F₁.Elements ⥤ F₂.Elements where
  obj t := ⟨t.1, α.app t.1 t.2⟩
  map {t₁ t₂} k := ⟨k.1, by simpa [map_snd] using (NatTrans.naturality_apply α k.1 t₁.2).symm⟩

@[simp]
/-
**CategoryTheory.CategoryOfElements.map_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.CategoryOfElements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_π {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : map α ⋙ π F₂ = π F₁ :=
  rfl

/-- The forward direction of the equivalence `F.Elements ≅ (*, F)`. -/
/-
**CategoryTheory.CategoryOfElements.toStructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.CategoryOfElements`。
形式化陈述：toStructuredArrow : F.Elements ⥤ StructuredArrow PUnit F where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forward direction of the equivalence `F.Elements ≅ (*, F)`.
-/
def toStructuredArrow : F.Elements ⥤ StructuredArrow PUnit F where
  obj X := StructuredArrow.mk <| ↾fun _ => X.2
  map {X Y} f := StructuredArrow.homMk f.val (by ext; simp [f.2])

@[simp]
/-
**CategoryTheory.CategoryOfElements.toStructuredArrow_obj** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.CategoryOfElements`。
形式化陈述：toStructuredArrow_obj (X) : (toStructuredArrow F).obj X = { left
参数：X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toStructuredArrow_obj (X) :
    (toStructuredArrow F).obj X =
      { left := ⟨⟨⟩⟩
        right := X.1
        hom := ↾fun _ => X.2 } :=
  rfl

@[simp]
/-
**CategoryTheory.CategoryOfElements.to_comma_map_right** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.CategoryOfElements`。
形式化陈述：to_comma_map_right {X Y} (f : X ⟶ Y) : ((toStructuredArrow F).map f).right
 = f.val
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem to_comma_map_right {X Y} (f : X ⟶ Y) : ((toStructuredArrow F).map f).right = f.val :=
  rfl

/-- The reverse direction of the equivalence `F.Elements ≅ (*, F)`. -/
/-
**CategoryTheory.CategoryOfElements.fromStructuredArrow** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.CategoryOfElements`。
形式化陈述：fromStructuredArrow : StructuredArrow PUnit F ⥤ F.Elements where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reverse direction of the equivalence `F.Elements ≅ (*, F)`.
-/
def fromStructuredArrow : StructuredArrow PUnit F ⥤ F.Elements where
  obj X := Functor.elementsMk _ X.right (X.hom .unit)
  map f := ⟨f.right, by simp [ConcreteCategory.congr_hom f.w.symm .unit]; rfl⟩

@[simp]
/-
**CategoryTheory.CategoryOfElements.fromStructuredArrow_obj** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.CategoryOfElements`。
形式化陈述：fromStructuredArrow_obj (X) : (fromStructuredArrow F).obj X = ⟨X.right, X.
hom PUnit.unit⟩
参数：X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromStructuredArrow_obj (X) : (fromStructuredArrow F).obj X = ⟨X.right, X.hom PUnit.unit⟩ :=
  rfl

@[simp]
/-
**CategoryTheory.CategoryOfElements.fromStructuredArrow_map** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.CategoryOfElements`。
形式化陈述：fromStructuredArrow_map {X Y} (f : X ⟶ Y) : (fromStructuredArrow F).map f 
= ⟨f.right, by simp [ConcreteCategory.congr_hom f.w.symm PUnit.unit]; rfl⟩
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromStructuredArrow_map {X Y} (f : X ⟶ Y) :
    (fromStructuredArrow F).map f =
      ⟨f.right, by simp [ConcreteCategory.congr_hom f.w.symm PUnit.unit]; rfl⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence between the category of elements `F.Elements`
and the comma category `(*, F)`. -/
@[simps]
/-
**CategoryTheory.CategoryOfElements.structuredArrowEquivalence** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.CategoryOfElements`。
形式化陈述：structuredArrowEquivalence : F.Elements ≌ StructuredArrow PUnit F where fu
nctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the category of elements `F.Elements`
and the comma category `(*, F)`.
-/
def structuredArrowEquivalence : F.Elements ≌ StructuredArrow PUnit F where
  functor := toStructuredArrow F
  inverse := fromStructuredArrow F
  unitIso := Iso.refl _
  counitIso := Iso.refl _

open Opposite

set_option backward.isDefEq.respectTransparency.types false in
/-- The forward direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaEquiv`.
-/
@[simps]
/-
**CategoryTheory.CategoryOfElements.toCostructuredArrow** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.CategoryOfElements`。
形式化陈述：toCostructuredArrow (F : Cᵒᵖ ⥤ Type v) : F.Elementsᵒᵖ ⥤ CostructuredArrow 
yoneda F where obj X
参数：F : Cᵒᵖ ⥤ Type v。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The forward direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaEquiv`.
-/
def toCostructuredArrow (F : Cᵒᵖ ⥤ Type v) : F.Elementsᵒᵖ ⥤ CostructuredArrow yoneda F where
  obj X := CostructuredArrow.mk (yonedaEquiv.symm (unop X).2)
  map f :=
    CostructuredArrow.homMk f.unop.val.unop (by
      ext Z y
      simp [yonedaEquiv])

set_option backward.defeqAttrib.useBackward true in
/-- The reverse direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaEquiv`.
-/
@[simps]
/-
**CategoryTheory.CategoryOfElements.fromCostructuredArrow** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.CategoryOfElements`。
形式化陈述：fromCostructuredArrow (F : Cᵒᵖ ⥤ Type v) : (CostructuredArrow yoneda F)ᵒᵖ 
⥤ F.Elements where obj X
参数：F : Cᵒᵖ ⥤ Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reverse direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaEquiv`.
-/
def fromCostructuredArrow (F : Cᵒᵖ ⥤ Type v) :
    (CostructuredArrow yoneda F)ᵒᵖ ⥤ F.Elements where
  obj X := ⟨op (unop X).1, yonedaEquiv.1 (unop X).3⟩
  map {X Y} f := ⟨f.unop.1.op, by simp [yonedaEquiv_naturality]⟩

@[simp]
/-
**CategoryTheory.CategoryOfElements.fromCostructuredArrow_obj_mk** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.CategoryOfElements`。
形式化陈述：fromCostructuredArrow_obj_mk (F : Cᵒᵖ ⥤ Type v) {X : C} (f : yoneda.obj X 
⟶ F) : (fromCostructuredArrow F).obj (op (CostructuredArrow.mk f)) = ⟨op X, yone
daEquiv.1 f⟩
参数：F : Cᵒᵖ ⥤ Type v；f : yoneda.obj X ⟶ F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromCostructuredArrow_obj_mk (F : Cᵒᵖ ⥤ Type v) {X : C} (f : yoneda.obj X ⟶ F) :
    (fromCostructuredArrow F).obj (op (CostructuredArrow.mk f)) = ⟨op X, yonedaEquiv.1 f⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)` given by yoneda lemma. -/
@[simps]
/-
**CategoryTheory.CategoryOfElements.costructuredArrowYonedaEquivalence** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.CategoryOfElements`。
形式化陈述：costructuredArrowYonedaEquivalence (F : Cᵒᵖ ⥤ Type v) : F.Elementsᵒᵖ ≌ Cos
tructuredArrow yoneda F where functor
参数：F : Cᵒᵖ ⥤ Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)` given by yoneda lemma.
-/
def costructuredArrowYonedaEquivalence (F : Cᵒᵖ ⥤ Type v) :
    F.Elementsᵒᵖ ≌ CostructuredArrow yoneda F where
  functor := toCostructuredArrow F
  inverse := (fromCostructuredArrow F).rightOp
  unitIso :=
    NatIso.ofComponents
      (fun X ↦ Iso.op (CategoryOfElements.isoMk _ _ (Iso.refl _) (by simp; rfl))) (by
        rintro ⟨x⟩ ⟨y⟩ ⟨f : y ⟶ x⟩
        exact Quiver.Hom.unop_inj (by ext; simp))
  counitIso := NatIso.ofComponents (fun X ↦ CostructuredArrow.isoMk (Iso.refl _) (by
    dsimp
    simpa only [Functor.map_id, Category.id_comp] using!
      (yonedaEquiv.symm_apply_apply X.hom).symm))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `(-.Elements)ᵒᵖ ≅ (yoneda, -)` of is actually a natural isomorphism of functors.
-/
/-
**CategoryTheory.CategoryOfElements.costructuredArrow_yoneda_equivalence_natural
ity** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CategoryOfElements`。
形式化陈述：costructuredArrow_yoneda_equivalence_naturality {F₁ F₂ : Cᵒᵖ ⥤ Type v} (α 
: F₁ ⟶ F₂) : (map α).op ⋙ toCostructuredArrow F₂ = toCostructuredArrow F₁ ⋙ Cost
ructuredArrow.map α
参数：α : F₁ ⟶ F₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.CostructuredArrow.eqToHom_left`：eqToHom_left {X Y : Costr
ucturedArrow S T} (h : X = Y) : (eqToHom h).left = eqToHom (by rw [h])
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The equivalence `(-.Elements)ᵒᵖ ≅ (yoneda, -)` of is actually a natural isomorph
ism of functors.
-/
theorem costructuredArrow_yoneda_equivalence_naturality {F₁ F₂ : Cᵒᵖ ⥤ Type v} (α : F₁ ⟶ F₂) :
    (map α).op ⋙ toCostructuredArrow F₂ = toCostructuredArrow F₁ ⋙ CostructuredArrow.map α := by
  fapply Functor.ext
  · intro X
    simp only [CostructuredArrow.map_mk, toCostructuredArrow_obj, Functor.op_obj,
      Functor.comp_obj]
    congr
    ext _ f
    exact (α.naturality_apply f.op (unop X).snd).symm
  · simp

/-- The equivalence `F.elementsᵒᵖ ≌ (yoneda, F)` is compatible with the forgetful functors. -/
@[simps!]
/-
**CategoryTheory.CategoryOfElements.costructuredArrowYonedaEquivalenceFunctorPro
j** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CategoryOfElements`。
形式化陈述：costructuredArrowYonedaEquivalenceFunctorProj (F : Cᵒᵖ ⥤ Type v) : (costru
cturedArrowYonedaEquivalence F).functor ⋙ CostructuredArrow.proj _ _ ≅ (π F).lef
tOp
参数：F : Cᵒᵖ ⥤ Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `F.elementsᵒᵖ ≌ (yoneda, F)` is compatible with the forgetful fu
nctors.
-/
def costructuredArrowYonedaEquivalenceFunctorProj (F : Cᵒᵖ ⥤ Type v) :
    (costructuredArrowYonedaEquivalence F).functor ⋙ CostructuredArrow.proj _ _ ≅ (π F).leftOp :=
  Iso.refl _

/-- The equivalence `F.elementsᵒᵖ ≌ (yoneda, F)` is compatible with the forgetful functors. -/
@[simps!]
/-
**CategoryTheory.CategoryOfElements.costructuredArrowYonedaEquivalenceInverse** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CategoryOfElements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `F.elementsᵒᵖ ≌ (yoneda, F)` is compatible with the forgetful fu
nctors.
-/
def costructuredArrowYonedaEquivalenceInverseπ (F : Cᵒᵖ ⥤ Type v) :
    (costructuredArrowYonedaEquivalence F).inverse ⋙ (π F).leftOp ≅ CostructuredArrow.proj _ _ :=
  Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The opposite of the category of elements of a presheaf of types
is equivalent to a category of costructured arrows for the Yoneda embedding functor. -/
@[simps]
/-
**CategoryTheory.CategoryOfElements.costructuredArrowULiftYonedaEquivalence** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CategoryOfElements`。
形式化陈述：costructuredArrowULiftYonedaEquivalence (F : Cᵒᵖ ⥤ Type (max w v)) : F.Ele
mentsᵒᵖ ≌ CostructuredArrow uliftYoneda.{w} F where functor
参数：F : Cᵒᵖ ⥤ Type (max w v)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The opposite of the category of elements of a presheaf of types
is equivalent to a category of costructured arrows for the Yoneda embedding func
tor.
-/
def costructuredArrowULiftYonedaEquivalence (F : Cᵒᵖ ⥤ Type (max w v)) :
    F.Elementsᵒᵖ ≌ CostructuredArrow uliftYoneda.{w} F where
  functor :=
    { obj x := CostructuredArrow.mk (uliftYonedaEquiv.{w}.symm x.unop.2)
      map f := CostructuredArrow.homMk f.1.1.unop (by
        dsimp
        rw [← uliftYonedaEquiv_symm_map, map_snd]) }
  inverse :=
    { obj X := op (F.elementsMk _ (uliftYonedaEquiv.{w} X.hom))
      map f := (homMk _ _ f.left.op (by
        dsimp
        rw [← CostructuredArrow.w f, uliftYonedaEquiv_naturality, Quiver.Hom.unop_op])).op }
  unitIso := NatIso.ofComponents (fun x ↦ Iso.op (isoMk _ _ (Iso.refl _) (by
    dsimp
    simpa only [Functor.map_id_apply] using
      uliftYonedaEquiv.apply_symm_apply (unop x).snd)))
    (fun f ↦ Quiver.Hom.unop_inj (by aesop))
  counitIso := NatIso.ofComponents (fun X ↦ CostructuredArrow.isoMk (Iso.refl _))

/-- The equivalence of categories `costructuredArrowULiftYonedaEquivalence`
commutes with the projections. -/
/-
**CategoryTheory.CategoryOfElements.costructuredArrowULiftYonedaEquivalenceFunct
orCompProjIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CategoryOfElements`。
形式化陈述：costructuredArrowULiftYonedaEquivalenceFunctorCompProjIso (F : Cᵒᵖ ⥤ Type 
(max w v)) : (costructuredArrowULiftYonedaEquivalence.{w} F).functor ⋙ Costructu
redArrow.proj _ _ ≅ (π F).leftOp
参数：F : Cᵒᵖ ⥤ Type (max w v)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories `costructuredArrowULiftYonedaEquivalence`
commutes with the projections.
-/
def costructuredArrowULiftYonedaEquivalenceFunctorCompProjIso (F : Cᵒᵖ ⥤ Type (max w v)) :
    (costructuredArrowULiftYonedaEquivalence.{w} F).functor ⋙ CostructuredArrow.proj _ _ ≅
      (π F).leftOp :=
  Iso.refl _

end CategoryOfElements

namespace Functor

/-- The initial object in `F.Elements` if `F` is representable. -/
@[simps]
/-
**CategoryTheory.Functor.Elements.initialOfRepresentableBy** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Functor.Elements`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor Cᵒᵖ (Type u_1)} → {X : C} → F.RepresentableBy X → F.Elements
参数：Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial object in `F.Elements` if `F` is representable.
-/
def Elements.initialOfRepresentableBy {F : Cᵒᵖ ⥤ Type*} {X : C} (h : F.RepresentableBy X) :
    F.Elements :=
  ⟨.op X, h.homEquiv (𝟙 X)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F` is represented by `X`, `X` with its universal element is the initial object of
`F.Elements.` -/
/-
**CategoryTheory.Functor.Elements.isInitialOfRepresentableBy** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor.Elements`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor Cᵒᵖ (Type u_1)} →       {X : C} →         (h : F.Representabl
eBy X) →           CategoryTheory.Limits.IsInitial (CategoryTheory.Functor.Eleme
nts.initialOfRepresentableBy h)
参数：Type u_1；h : F.RepresentableBy X；CategoryTheory.Functor.Elements.initialOfRep
resentableBy h。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F` is represented by `X`, `X` with its universal element is the initial obje
ct of
`F.Elements.`
-/
def Elements.isInitialOfRepresentableBy {F : Cᵒᵖ ⥤ Type*} {X : C} (h : F.RepresentableBy X) :
    Limits.IsInitial (initialOfRepresentableBy h) :=
  .ofUniqueHom (fun Y ↦ ⟨h.homEquiv.symm Y.snd |>.op, by simp [← h.homEquiv_comp]⟩) fun Y m ↦ by
    simp [← m.2, ← h.homEquiv_unop_comp]

/-- The initial object in `F.Elements` if `F` is corepresentable. -/
@[simps]
/-
**CategoryTheory.Functor.Elements.initialOfCorepresentableBy** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor.Elements`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor C (Type u_1)} → {X : C} → F.CorepresentableBy X → F.Elements
参数：Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial object in `F.Elements` if `F` is corepresentable.
-/
def Elements.initialOfCorepresentableBy {F : C ⥤ Type*} {X : C} (h : F.CorepresentableBy X) :
    F.Elements :=
  ⟨X, h.homEquiv (𝟙 X)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F` is corepresented by `X`, `X` with its universal element is the initial object of
`F.Elements.` -/
/-
**CategoryTheory.Functor.Elements.isInitialOfCorepresentableBy** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Functor.Elements`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor C (Type u_1)} →       {X : C} →         (h : F.Corepresentabl
eBy X) →           CategoryTheory.Limits.IsInitial (CategoryTheory.Functor.Eleme
nts.initialOfCorepresentableBy h)
参数：Type u_1；h : F.CorepresentableBy X；CategoryTheory.Functor.Elements.initialOfC
orepresentableBy h。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F` is corepresented by `X`, `X` with its universal element is the initial ob
ject of
`F.Elements.`
-/
def Elements.isInitialOfCorepresentableBy {F : C ⥤ Type*} {X : C} (h : F.CorepresentableBy X) :
    Limits.IsInitial (initialOfCorepresentableBy h) :=
  .ofUniqueHom (fun Y ↦ ⟨h.homEquiv.symm Y.snd, by simp [← h.homEquiv_comp]⟩) fun Y m ↦ by
    simp [← m.2, ← h.homEquiv_comp]

/--
The initial object in the category of elements for a representable functor. In `isInitial` it is
shown that this is initial.
-/
/-
**CategoryTheory.Functor.Elements.initial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.Elements`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → (A : C) → (Cate
goryTheory.yoneda.obj A).Elements
参数：A : C；CategoryTheory.yoneda.obj A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial object in the category of elements for a representable functor. In `
isInitial` it is
shown that this is initial.
-/
def Elements.initial (A : C) : (yoneda.obj A).Elements :=
  ⟨Opposite.op A, 𝟙 _⟩

/-- Show that `Elements.initial A` is initial in the category of elements for the `yoneda` functor.
-/
/-
**CategoryTheory.Functor.Elements.isInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor.Elements`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (A : C) →
 CategoryTheory.Limits.IsInitial (CategoryTheory.Functor.Elements.initial A)
参数：A : C；CategoryTheory.Functor.Elements.initial A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show that `Elements.initial A` is initial in the category of elements for the `y
oneda` functor.
-/
def Elements.isInitial (A : C) : Limits.IsInitial (Elements.initial A) :=
  isInitialOfRepresentableBy (.yoneda A)

/-- The functor `(F ⋙ G).Elements ⥤ G.Elements`. -/
@[simps]
/-
**CategoryTheory.Functor.Elements.precomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.Elements`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{u_2, u_1} D] →         (F : Cat
egoryTheory.Functor C D) →           (G : CategoryTheory.Functor D (Type w)) → C
ategoryTheory.Functor (F.comp G).Elements G.Elements
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D (Type w)；F.comp G
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `(F ⋙ G).Elements ⥤ G.Elements`.
-/
def Elements.precomp {D : Type*} [Category D] (F : C ⥤ D) (G : D ⥤ Type w) :
    (F ⋙ G).Elements ⥤ G.Elements where
  obj x := G.elementsMk (F.obj x.fst) x.snd
  map f := ⟨F.map f.1, f.2⟩
/-
**CategoryTheory.Functor.Elements.essentiallySmall** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor.Elements`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (F : CategoryTheo
ry.Functor C (Type w))   [CategoryTheory.EssentiallySmall.{w, v, u} C], Category
Theory.EssentiallySmall.{w, v, max u w} F.Elements
参数：F : CategoryTheory.Functor C (Type w)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.essentiallySmall_iff_objectPropertyEssentiallySmall_top`：
∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Locally
Small.{w, v, u} C],   CategoryTheory.EssentiallySmall.{w, v,…
· 使用定理 `CategoryTheory.CategoryOfElements.instLocallySmallElements`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v,
 u} C]   (F : CategoryTheory.Functor C (Type w))…
· 使用定理 `CategoryTheory.locallySmall_of_essentiallySmall`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.EssentiallySmall.{w, v, u} C],
   CategoryTheory.LocallySmall.{w, v,…
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le'`：∀ {C : 
Type u} {inst : CategoryTheory.Category.{v, u} C} (P : CategoryTheory.ObjectProp
erty C)   [self : CategoryTheory.ObjectProperty.Essen…
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallTopOfEssentiallySmall`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Essent
iallySmall.{w, v, u} C],   CategoryTheory.ObjectProperty.Esse…
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance Elements.essentiallySmall {C : Type u} [Category.{v} C]
    (F : C ⥤ Type w) [EssentiallySmall.{w} C] :
    EssentiallySmall.{w} F.Elements := by
  rw [essentiallySmall_iff_objectPropertyEssentiallySmall_top]
  obtain ⟨P, _, hP⟩ := ObjectProperty.EssentiallySmall.exists_small_le' (⊤ : ObjectProperty C)
  refine ⟨fun x ↦ P x.1, ?_, fun y _ ↦ ?_⟩
  · exact small_of_surjective.{w} (α := Σ (Z : Subtype P), F.obj Z.1)
      (f := fun x ↦ ⟨F.elementsMk _ x.2, x.1.2⟩)
      (fun ⟨x, hx⟩ ↦ ⟨⟨⟨x.1, hx⟩, x.2⟩, rfl⟩)
  · obtain ⟨Z, hZ, ⟨e⟩⟩ := hP y.fst (by simp)
    exact ⟨F.elementsMk Z (F.map e.hom y.snd), hZ,
      ⟨CategoryOfElements.isoMk _ _ e rfl⟩⟩

end Functor

end CategoryTheory

