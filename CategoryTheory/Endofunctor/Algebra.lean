/-
Copyright (c) 2022 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta, Johan Commelin, Reid Barton, Robert Y. Lewis, Joseph Hua
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!

# Algebras of endofunctors

This file defines (co)algebras of an endofunctor, and provides the category instance for them.
It also defines the forgetful functor from the category of (co)algebras. It is shown that the
structure map of the initial algebra of an endofunctor is an isomorphism. Furthermore, it is shown
that for an adjunction `F ⊣ G` the category of algebras over `F` is equivalent to the category of
coalgebras over `G`.

## TODO

* Prove that if the countable infinite product over the powers of the endofunctor exists, then
  algebras over the endofunctor coincide with algebras over the free monad on the endofunctor.
-/

@[expose] public section


universe v u

namespace CategoryTheory

namespace Endofunctor

variable {C : Type u} [Category.{v} C]

/-- An algebra of an endofunctor; `str` stands for "structure morphism" -/
/-
**CategoryTheory.Endofunctor.Algebra** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
.Endofunctor`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Functor C C → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra of an endofunctor; `str` stands for "structure morphism"
-/
structure Algebra (F : C ⥤ C) where
  /-- carrier of the algebra -/
  a : C
  /-- structure morphism of the algebra -/
  str : F.obj a ⟶ a
/-
**CategoryTheory.Endofunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Endofunc
tor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited C] : Inhabited (Algebra (𝟭 C)) :=
  ⟨⟨default, 𝟙 _⟩⟩

namespace Algebra

variable {F : C ⥤ C} (A : Algebra F) {A₀ A₁ A₂ : Algebra F}

/-
```
        str
   F A₀ -----> A₀
    |          |
F f |          | f
    V          V
   F A₁ -----> A₁
        str
```
-/
/-- A morphism between algebras of endofunctor `F` -/
@[ext]
/-
**CategoryTheory.Endofunctor.Algebra.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheo
ry.Endofunctor.Algebra`。
形式化陈述：Hom (A₀ A₁ : Algebra F) where /-- underlying morphism between the carriers
 -/ f : A₀.1 ⟶ A₁.1 /-- compatibility condition -/ h : F.map f ≫ A₁.str = A₀.str
 ≫ f
参数：A₀ A₁ : Algebra F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism between algebras of endofunctor `F`
-/
structure Hom (A₀ A₁ : Algebra F) where
  /-- underlying morphism between the carriers -/
  f : A₀.1 ⟶ A₁.1
  /-- compatibility condition -/
  h : F.map f ≫ A₁.str = A₀.str ≫ f := by cat_disch

attribute [reassoc (attr := simp)] Hom.h

namespace Hom

/-- The identity morphism of an algebra of endofunctor `F` -/
/-
**CategoryTheory.Endofunctor.Algebra.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Endofunctor.Algebra.Hom`。
形式化陈述：id : Hom A A where f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism of an algebra of endofunctor `F`
-/
def id : Hom A A where f := 𝟙 _
/-
**CategoryTheory.Endofunctor.Algebra.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Endofunctor.Algebra.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Hom A A) :=
  ⟨{ f := 𝟙 _ }⟩

/-- The composition of morphisms between algebras of endofunctor `F` -/
/-
**CategoryTheory.Endofunctor.Algebra.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Endofunctor.Algebra.Hom`。
形式化陈述：comp (f : Hom A₀ A₁) (g : Hom A₁ A₂) : Hom A₀ A₂ where f
参数：f : Hom A₀ A₁；g : Hom A₁ A₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of morphisms between algebras of endofunctor `F`
-/
def comp (f : Hom A₀ A₁) (g : Hom A₁ A₂) : Hom A₀ A₂ where f := f.1 ≫ g.1

end Hom

/-
**CategoryTheory.Endofunctor.Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Endofunctor.Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ C) : CategoryStruct (Algebra F) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
/-
**CategoryTheory.Endofunctor.Algebra.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Endofunctor.Algebra`。
形式化陈述：ext {A B : Algebra F} {f g : A ⟶ B} (w : f.f = g.f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Endofunctor.Algebra.Hom.ext`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {F : CategoryTheory.Functor C C}   {A₀ A₁ : Categor
yTheory.Endofunctor.Algebra F} {…
-/
lemma ext {A B : Algebra F} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch) : f = g :=
  Hom.ext w

@[simp]
/-
**CategoryTheory.Endofunctor.Algebra.id_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Endofunctor.Algebra`。
形式化陈述：id_eq_id : Algebra.Hom.id A = 𝟙 A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_eq_id : Algebra.Hom.id A = 𝟙 A :=
  rfl

@[simp]
/-
**CategoryTheory.Endofunctor.Algebra.id_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Endofunctor.Algebra`。
形式化陈述：id_f : (𝟙 _ : A ⟶ A).1 = 𝟙 A.1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_f : (𝟙 _ : A ⟶ A).1 = 𝟙 A.1 :=
  rfl

variable (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂)

@[simp]
/-
**CategoryTheory.Endofunctor.Algebra.comp_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Endofunctor.Algebra`。
形式化陈述：comp_eq_comp : Algebra.Hom.comp f g = f ≫ g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_eq_comp : Algebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
/-
**CategoryTheory.Endofunctor.Algebra.comp_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Endofunctor.Algebra`。
形式化陈述：comp_f : (f ≫ g).1 = f.1 ≫ g.1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_f : (f ≫ g).1 = f.1 ≫ g.1 :=
  rfl

/-- Algebras of an endofunctor `F` form a category -/
/-
**CategoryTheory.Endofunctor.Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Endofunctor.Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebras of an endofunctor `F` form a category
-/
instance (F : C ⥤ C) : Category (Algebra F) := { }

/-- To construct an isomorphism of algebras, it suffices to give an isomorphism of the As which
commutes with the structure morphisms.
-/
@[simps!]
/-
**CategoryTheory.Endofunctor.Algebra.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Endofunctor.Algebra`。
形式化陈述：isoMk (h : A₀.1 ≅ A₁.1) (w : F.map h.hom ≫ A₁.str = A₀.str ≫ h.hom
参数：h : A₀.1 ≅ A₁.1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct an isomorphism of algebras, it suffices to give an isomorphism of t
he As which
commutes with the structure morphisms.
-/
def isoMk (h : A₀.1 ≅ A₁.1) (w : F.map h.hom ≫ A₁.str = A₀.str ≫ h.hom := by cat_disch) :
    A₀ ≅ A₁ where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_comp_inv, Category.assoc, ← w, ← Functor.map_comp_assoc]
        simp }

/-- The forgetful functor from the category of algebras, forgetting the algebraic structure. -/
@[simps]
/-
**CategoryTheory.Endofunctor.Algebra.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Endofunctor.Algebra`。
形式化陈述：forget (F : C ⥤ C) : Algebra F ⥤ C where obj A
参数：F : C ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the category of algebras, forgetting the algebraic st
ructure.
-/
def forget (F : C ⥤ C) : Algebra F ⥤ C where
  obj A := A.1
  map := Hom.f

/-- An algebra morphism with an underlying isomorphism hom in `C` is an algebra isomorphism. -/
/-
**CategoryTheory.Endofunctor.Algebra.iso_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Endofunctor.Algebra`。
形式化陈述：iso_of_iso (f : A₀ ⟶ A₁) [IsIso f.1] : IsIso f
参数：f : A₀ ⟶ A₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Endofunctor.Algebra.Hom.h`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {F : CategoryTheory.Functor C C}   {A₀ A₁ : CategoryT
heory.Endofunctor.Algebra F} (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Endofunctor.Algebra.ext`：ext {A B : Algebra F} {f g : A ⟶
 B} (w : f.f = g.f
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y

--- 原说明 ---
An algebra morphism with an underlying isomorphism hom in `C` is an algebra isom
orphism.
-/
theorem iso_of_iso (f : A₀ ⟶ A₁) [IsIso f.1] : IsIso f :=
  ⟨⟨{ f := inv f.1
      h := by simp }, by cat_disch, by cat_disch⟩⟩
/-
**CategoryTheory.Endofunctor.Algebra.forget_reflects_iso** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Endofunctor.Algebra`。
形式化陈述：forget_reflects_iso : (forget F).ReflectsIsomorphisms where reflects
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Endofunctor.Algebra.iso_of_iso`：iso_of_iso (f : A₀ ⟶ A₁) 
[IsIso f.1] : IsIso f
-/
instance forget_reflects_iso : (forget F).ReflectsIsomorphisms where reflects := iso_of_iso
/-
**CategoryTheory.Endofunctor.Algebra.forget_faithful** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Endofunctor.Algebra`。
形式化陈述：forget_faithful : (forget F).Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Endofunctor.Algebra.ext`：ext {A B : Algebra F} {f g : A ⟶
 B} (w : f.f = g.f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Endofunctor.Algebra.forget_map`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] (F : CategoryTheory.Functor C C)   {X Y : Catego
ryTheory.Endofunctor.Algebra F} (se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance forget_faithful : (forget F).Faithful := { }

/-- An algebra morphism with an underlying epimorphism hom in `C` is an algebra epimorphism. -/
/-
**CategoryTheory.Endofunctor.Algebra.epi_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Endofunctor.Algebra`。
形式化陈述：epi_of_epi {X Y : Algebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
An algebra morphism with an underlying epimorphism hom in `C` is an algebra epim
orphism.
-/
theorem epi_of_epi {X Y : Algebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f :=
  (forget F).epi_of_epi_map h

/-- An algebra morphism with an underlying monomorphism hom in `C` is an algebra monomorphism. -/
/-
**CategoryTheory.Endofunctor.Algebra.mono_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Endofunctor.Algebra`。
形式化陈述：mono_of_mono {X Y : Algebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
An algebra morphism with an underlying monomorphism hom in `C` is an algebra mon
omorphism.
-/
theorem mono_of_mono {X Y : Algebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f :=
  (forget F).mono_of_mono_map h

/-- From a natural transformation `α : G → F` we get a functor from
algebras of `F` to algebras of `G`.
-/
@[simps]
/-
**CategoryTheory.Endofunctor.Algebra.functorOfNatTrans** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Endofunctor.Algebra`。
形式化陈述：functorOfNatTrans {F G : C ⥤ C} (α : G ⟶ F) : Algebra F ⥤ Algebra G where 
obj A
参数：α : G ⟶ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a natural transformation `α : G → F` we get a functor from
algebras of `F` to algebras of `G`.
-/
def functorOfNatTrans {F G : C ⥤ C} (α : G ⟶ F) : Algebra F ⥤ Algebra G where
  obj A :=
    { a := A.1
      str := α.app _ ≫ A.str }
  map f := { f := f.1 }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The identity transformation induces the identity endofunctor on the category of algebras. -/
@[simps!]
/-
**CategoryTheory.Endofunctor.Algebra.functorOfNatTransId** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Endofunctor.Algebra`。
形式化陈述：functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity transformation induces the identity endofunctor on the category of 
algebras.
-/
def functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A composition of natural transformations gives the composition of corresponding functors. -/
@[simps!]
/-
**CategoryTheory.Endofunctor.Algebra.functorOfNatTransComp** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Endofunctor.Algebra`。
形式化陈述：functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) : fun
ctorOfNatTrans (α ≫ β) ≅ functorOfNatTrans β ⋙ functorOfNatTrans α
参数：α : F₀ ⟶ F₁；β : F₁ ⟶ F₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A composition of natural transformations gives the composition of corresponding 
functors.
-/
def functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
    functorOfNatTrans (α ≫ β) ≅ functorOfNatTrans β ⋙ functorOfNatTrans α :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/--
If `α` and `β` are two equal natural transformations, then the functors of algebras induced by them
are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps!]
/-
**CategoryTheory.Endofunctor.Algebra.functorOfNatTransEq** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Endofunctor.Algebra`。
形式化陈述：functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) : functorOfNat
Trans α ≅ functorOfNatTrans β
参数：h : α = β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` and `β` are two equal natural transformations, then the functors of algeb
ras induced by them
are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components ar
e nicer to prove
lemmas about.
-/
def functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) :
    functorOfNatTrans α ≅ functorOfNatTrans β :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- Naturally isomorphic endofunctors give equivalent categories of algebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
@[simps]
/-
**CategoryTheory.Endofunctor.Algebra.equivOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Endofunctor.Algebra`。
形式化陈述：equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Algebra F ≌ Algebra G where func
tor
参数：α : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Naturally isomorphic endofunctors give equivalent categories of algebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
def equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Algebra F ≌ Algebra G where
  functor := functorOfNatTrans α.inv
  inverse := functorOfNatTrans α.hom
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId

namespace Initial

variable {A : Algebra F} (h : Limits.IsInitial A)
/-- The inverse of the structure map of an initial algebra -/
@[simp]
/-
**CategoryTheory.Endofunctor.Algebra.Initial.strInv** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Endofunctor.Algebra.Initial`。
形式化陈述：strInv : A.1 ⟶ F.obj A.1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of the structure map of an initial algebra
-/
def strInv : A.1 ⟶ F.obj A.1 :=
  (h.to ⟨F.obj A.a, F.map A.str⟩).f
/-
**CategoryTheory.Endofunctor.Algebra.Initial.left_inv'** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Endofunctor.Algebra.Initial`。
形式化陈述：left_inv' : ⟨strInv h ≫ A.str, by rw [← Category.assoc, F.map_comp, strInv
, ← Hom.h]⟩ = 𝟙 A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
-/
theorem left_inv' :
    ⟨strInv h ≫ A.str, by rw [← Category.assoc, F.map_comp, strInv, ← Hom.h]⟩ = 𝟙 A :=
  Limits.IsInitial.hom_ext h _ (𝟙 A)
/-
**CategoryTheory.Endofunctor.Algebra.Initial.left_inv** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Endofunctor.Algebra.Initial`。
形式化陈述：left_inv : strInv h ≫ A.str = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Endofunctor.Algebra.Initial.left_inv'`：left_inv' : ⟨strIn
v h ≫ A.str, by rw [← Category.assoc, F.map_comp, strInv, ← Hom.h]⟩ = 𝟙 A
-/
theorem left_inv : strInv h ≫ A.str = 𝟙 _ :=
  congr_arg Hom.f (left_inv' h)
/-
**CategoryTheory.Endofunctor.Algebra.Initial.right_inv** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Endofunctor.Algebra.Initial`。
形式化陈述：right_inv : A.str ≫ strInv h = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Endofunctor.Algebra.Initial.strInv.eq_1`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor C C}   {A :
 CategoryTheory.Endofunctor.Algebra F} (h : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Endofunctor.Algebra.Hom.h`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {F : CategoryTheory.Functor C C}   {A₀ A₁ : CategoryT
heory.Endofunctor.Algebra F} (…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Endofunctor.Algebra.Initial.left_inv`：left_inv : strInv h
 ≫ A.str = 𝟙 _
-/
theorem right_inv : A.str ≫ strInv h = 𝟙 _ := by
  rw [strInv, ← (h.to ⟨F.obj A.1, F.map A.str⟩).h, ← F.map_id, ← F.map_comp]
  congr
  exact left_inv h

/-- The structure map of the initial algebra is an isomorphism,
hence endofunctors preserve their initial algebras
-/
/-
**CategoryTheory.Endofunctor.Algebra.Initial.str_isIso** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Endofunctor.Algebra.Initial`。
形式化陈述：str_isIso (h : Limits.IsInitial A) : IsIso A.str
参数：h : Limits.IsInitial A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Endofunctor.Algebra.Initial.right_inv`：right_inv : A.str 
≫ strInv h = 𝟙 _
· 使用定理 `CategoryTheory.Endofunctor.Algebra.Initial.left_inv`：left_inv : strInv h
 ≫ A.str = 𝟙 _

--- 原说明 ---
The structure map of the initial algebra is an isomorphism,
hence endofunctors preserve their initial algebras
-/
theorem str_isIso (h : Limits.IsInitial A) : IsIso A.str :=
  { out := ⟨strInv h, right_inv _, left_inv _⟩ }

end Initial

end Algebra

/-- A coalgebra of an endofunctor; `str` stands for "structure morphism" -/
/-
**CategoryTheory.Endofunctor.Coalgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Endofunctor`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Functor C C → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coalgebra of an endofunctor; `str` stands for "structure morphism"
-/
structure Coalgebra (F : C ⥤ C) where
  /-- carrier of the coalgebra -/
  V : C
  /-- structure morphism of the coalgebra -/
  str : V ⟶ F.obj V
/-
**CategoryTheory.Endofunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Endofunc
tor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited C] : Inhabited (Coalgebra (𝟭 C)) :=
  ⟨⟨default, 𝟙 _⟩⟩

namespace Coalgebra

variable {F : C ⥤ C} (V : Coalgebra F) {V₀ V₁ V₂ : Coalgebra F}

/-
```
        str
    V₀ -----> F V₀
    |          |
  f |          | F f
    V          V
    V₁ -----> F V₁
        str
```
-/
/-- A morphism between coalgebras of an endofunctor `F` -/
@[ext]
/-
**CategoryTheory.Endofunctor.Coalgebra.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTh
eory.Endofunctor.Coalgebra`。
形式化陈述：Hom (V₀ V₁ : Coalgebra F) where /-- underlying morphism between two carrie
rs -/ f : V₀.1 ⟶ V₁.1 /-- compatibility condition -/ h : V₀.str ≫ F.map f = f ≫ 
V₁.str
参数：V₀ V₁ : Coalgebra F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism between coalgebras of an endofunctor `F`
-/
structure Hom (V₀ V₁ : Coalgebra F) where
  /-- underlying morphism between two carriers -/
  f : V₀.1 ⟶ V₁.1
  /-- compatibility condition -/
  h : V₀.str ≫ F.map f = f ≫ V₁.str := by cat_disch

attribute [reassoc (attr := simp)] Hom.h

namespace Hom

/-- The identity morphism of an algebra of endofunctor `F` -/
/-
**CategoryTheory.Endofunctor.Coalgebra.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Endofunctor.Coalgebra.Hom`。
形式化陈述：id : Hom V V where f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism of an algebra of endofunctor `F`
-/
def id : Hom V V where f := 𝟙 _
/-
**CategoryTheory.Endofunctor.Coalgebra.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Endofunctor.Coalgebra.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Hom V V) :=
  ⟨{ f := 𝟙 _ }⟩

/-- The composition of morphisms between algebras of endofunctor `F` -/
/-
**CategoryTheory.Endofunctor.Coalgebra.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Endofunctor.Coalgebra.Hom`。
形式化陈述：comp (f : Hom V₀ V₁) (g : Hom V₁ V₂) : Hom V₀ V₂ where f
参数：f : Hom V₀ V₁；g : Hom V₁ V₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of morphisms between algebras of endofunctor `F`
-/
def comp (f : Hom V₀ V₁) (g : Hom V₁ V₂) : Hom V₀ V₂ where f := f.1 ≫ g.1

end Hom

/-
**CategoryTheory.Endofunctor.Coalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Endofunctor.Coalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ C) : CategoryStruct (Coalgebra F) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
/-
**CategoryTheory.Endofunctor.Coalgebra.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Endofunctor.Coalgebra`。
形式化陈述：ext {A B : Coalgebra F} {f g : A ⟶ B} (w : f.f = g.f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Endofunctor.Coalgebra.Hom.ext`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} {F : CategoryTheory.Functor C C}   {V₀ V₁ : Categ
oryTheory.Endofunctor.Coalgebra F}…
-/
lemma ext {A B : Coalgebra F} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch) : f = g :=
  Hom.ext w

@[simp]
/-
**CategoryTheory.Endofunctor.Coalgebra.id_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Endofunctor.Coalgebra`。
形式化陈述：id_eq_id : Coalgebra.Hom.id V = 𝟙 V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_eq_id : Coalgebra.Hom.id V = 𝟙 V :=
  rfl

@[simp]
/-
**CategoryTheory.Endofunctor.Coalgebra.id_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Endofunctor.Coalgebra`。
形式化陈述：id_f : (𝟙 _ : V ⟶ V).1 = 𝟙 V.1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_f : (𝟙 _ : V ⟶ V).1 = 𝟙 V.1 :=
  rfl

variable (f : V₀ ⟶ V₁) (g : V₁ ⟶ V₂)

@[simp]
/-
**CategoryTheory.Endofunctor.Coalgebra.comp_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Endofunctor.Coalgebra`。
形式化陈述：comp_eq_comp : Coalgebra.Hom.comp f g = f ≫ g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_eq_comp : Coalgebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
/-
**CategoryTheory.Endofunctor.Coalgebra.comp_f** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Endofunctor.Coalgebra`。
形式化陈述：comp_f : (f ≫ g).1 = f.1 ≫ g.1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_f : (f ≫ g).1 = f.1 ≫ g.1 :=
  rfl

/-- Coalgebras of an endofunctor `F` form a category -/
/-
**CategoryTheory.Endofunctor.Coalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Endofunctor.Coalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coalgebras of an endofunctor `F` form a category
-/
instance (F : C ⥤ C) : Category (Coalgebra F) := { }

/-- To construct an isomorphism of coalgebras, it suffices to give an isomorphism of the Vs which
commutes with the structure morphisms.
-/
@[simps]
/-
**CategoryTheory.Endofunctor.Coalgebra.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Endofunctor.Coalgebra`。
形式化陈述：isoMk (h : V₀.1 ≅ V₁.1) (w : V₀.str ≫ F.map h.hom = h.hom ≫ V₁.str
参数：h : V₀.1 ≅ V₁.1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct an isomorphism of coalgebras, it suffices to give an isomorphism of
 the Vs which
commutes with the structure morphisms.
-/
def isoMk (h : V₀.1 ≅ V₁.1) (w : V₀.str ≫ F.map h.hom = h.hom ≫ V₁.str := by cat_disch) :
    V₀ ≅ V₁ where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_inv_comp, ← Category.assoc, ← w, Category.assoc, ← F.map_comp]
        simp only [Iso.hom_inv_id, Functor.map_id, Category.comp_id] }

/-- The forgetful functor from the category of coalgebras, forgetting the coalgebraic structure. -/
@[simps]
/-
**CategoryTheory.Endofunctor.Coalgebra.forget** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Endofunctor.Coalgebra`。
形式化陈述：forget (F : C ⥤ C) : Coalgebra F ⥤ C where obj A
参数：F : C ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the category of coalgebras, forgetting the coalgebrai
c structure.
-/
def forget (F : C ⥤ C) : Coalgebra F ⥤ C where
  obj A := A.1
  map f := f.1

/-- A coalgebra morphism with an underlying isomorphism hom in `C` is a coalgebra isomorphism. -/
/-
**CategoryTheory.Endofunctor.Coalgebra.iso_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Endofunctor.Coalgebra`。
形式化陈述：iso_of_iso (f : V₀ ⟶ V₁) [IsIso f.1] : IsIso f
参数：f : V₀ ⟶ V₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.eq_inv_comp`：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Endofunctor.Coalgebra.Hom.h`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {F : CategoryTheory.Functor C C}   {V₀ V₁ : Categor
yTheory.Endofunctor.Coalgebra F}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Endofunctor.Coalgebra.ext`：ext {A B : Coalgebra F} {f g :
 A ⟶ B} (w : f.f = g.f
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y

--- 原说明 ---
A coalgebra morphism with an underlying isomorphism hom in `C` is a coalgebra is
omorphism.
-/
theorem iso_of_iso (f : V₀ ⟶ V₁) [IsIso f.1] : IsIso f :=
  ⟨⟨{ f := inv f.1
      h := by
        rw [IsIso.eq_inv_comp f.1, ← Category.assoc, ← f.h, Category.assoc]
        simp }, by cat_disch, by cat_disch⟩⟩
/-
**CategoryTheory.Endofunctor.Coalgebra.forget_reflects_iso** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Endofunctor.Coalgebra`。
形式化陈述：forget_reflects_iso : (forget F).ReflectsIsomorphisms where reflects
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Endofunctor.Coalgebra.iso_of_iso`：iso_of_iso (f : V₀ ⟶ V₁
) [IsIso f.1] : IsIso f
-/
instance forget_reflects_iso : (forget F).ReflectsIsomorphisms where reflects := iso_of_iso
/-
**CategoryTheory.Endofunctor.Coalgebra.forget_faithful** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Endofunctor.Coalgebra`。
形式化陈述：forget_faithful : (forget F).Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Endofunctor.Coalgebra.ext`：ext {A B : Coalgebra F} {f g :
 A ⟶ B} (w : f.f = g.f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Endofunctor.Coalgebra.forget_map`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] (F : CategoryTheory.Functor C C)   {X Y : Cate
goryTheory.Endofunctor.Coalgebra F} (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance forget_faithful : (forget F).Faithful := { }

/-- An algebra morphism with an underlying epimorphism hom in `C` is an algebra epimorphism. -/
/-
**CategoryTheory.Endofunctor.Coalgebra.epi_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Endofunctor.Coalgebra`。
形式化陈述：epi_of_epi {X Y : Coalgebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
An algebra morphism with an underlying epimorphism hom in `C` is an algebra epim
orphism.
-/
theorem epi_of_epi {X Y : Coalgebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f :=
  (forget F).epi_of_epi_map h

/-- An algebra morphism with an underlying monomorphism hom in `C` is an algebra monomorphism. -/
/-
**CategoryTheory.Endofunctor.Coalgebra.mono_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Endofunctor.Coalgebra`。
形式化陈述：mono_of_mono {X Y : Coalgebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
An algebra morphism with an underlying monomorphism hom in `C` is an algebra mon
omorphism.
-/
theorem mono_of_mono {X Y : Coalgebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f :=
  (forget F).mono_of_mono_map h

/-- From a natural transformation `α : F → G` we get a functor from
coalgebras of `F` to coalgebras of `G`.
-/
@[simps]
/-
**CategoryTheory.Endofunctor.Coalgebra.functorOfNatTrans** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Endofunctor.Coalgebra`。
形式化陈述：functorOfNatTrans {F G : C ⥤ C} (α : F ⟶ G) : Coalgebra F ⥤ Coalgebra G wh
ere obj V
参数：α : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a natural transformation `α : F → G` we get a functor from
coalgebras of `F` to coalgebras of `G`.
-/
def functorOfNatTrans {F G : C ⥤ C} (α : F ⟶ G) : Coalgebra F ⥤ Coalgebra G where
  obj V :=
    { V := V.1
      str := V.str ≫ α.app V.1 }
  map f :=
    { f := f.1
      h := by rw [Category.assoc, ← α.naturality, ← Category.assoc, f.h, Category.assoc] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The identity transformation induces the identity endofunctor on the category of coalgebras. -/
@[simps!]
/-
**CategoryTheory.Endofunctor.Coalgebra.functorOfNatTransId** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Endofunctor.Coalgebra`。
形式化陈述：functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity transformation induces the identity endofunctor on the category of 
coalgebras.
-/
def functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A composition of natural transformations gives the composition of corresponding functors. -/
@[simps!]
/-
**CategoryTheory.Endofunctor.Coalgebra.functorOfNatTransComp** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Endofunctor.Coalgebra`。
形式化陈述：functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) : fun
ctorOfNatTrans (α ≫ β) ≅ functorOfNatTrans α ⋙ functorOfNatTrans β
参数：α : F₀ ⟶ F₁；β : F₁ ⟶ F₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A composition of natural transformations gives the composition of corresponding 
functors.
-/
def functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
    functorOfNatTrans (α ≫ β) ≅ functorOfNatTrans α ⋙ functorOfNatTrans β :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `α` and `β` are two equal natural transformations, then the functors of coalgebras induced by
them are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps!]
/-
**CategoryTheory.Endofunctor.Coalgebra.functorOfNatTransEq** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Endofunctor.Coalgebra`。
形式化陈述：functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) : functorOfNat
Trans α ≅ functorOfNatTrans β
参数：h : α = β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` and `β` are two equal natural transformations, then the functors of coalg
ebras induced by
them are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components ar
e nicer to prove
lemmas about.
-/
def functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) :
    functorOfNatTrans α ≅ functorOfNatTrans β :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- Naturally isomorphic endofunctors give equivalent categories of coalgebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
@[simps]
/-
**CategoryTheory.Endofunctor.Coalgebra.equivOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Endofunctor.Coalgebra`。
形式化陈述：equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Coalgebra F ≌ Coalgebra G where 
functor
参数：α : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Naturally isomorphic endofunctors give equivalent categories of coalgebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
def equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Coalgebra F ≌ Coalgebra G where
  functor := functorOfNatTrans α.hom
  inverse := functorOfNatTrans α.inv
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId

namespace Terminal

variable {A : Coalgebra F} (h : Limits.IsTerminal A)

/-- The inverse of the structure map of a terminal coalgebra -/
@[simp]
/-
**CategoryTheory.Endofunctor.Coalgebra.Terminal.strInv** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Endofunctor.Coalgebra.Terminal`。
形式化陈述：strInv : F.obj A.1 ⟶ A.1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of the structure map of a terminal coalgebra
-/
def strInv : F.obj A.1 ⟶ A.1 :=
  (h.from ⟨F.obj A.V, F.map A.str⟩).f
/-
**CategoryTheory.Endofunctor.Coalgebra.Terminal.right_inv'** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Endofunctor.Coalgebra.Terminal`。
形式化陈述：right_inv' : ⟨A.str ≫ strInv h, by rw [Category.assoc, F.map_comp, strInv,
 ← Hom.h] ⟩ = 𝟙 A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
-/
theorem right_inv' :
    ⟨A.str ≫ strInv h, by rw [Category.assoc, F.map_comp, strInv, ← Hom.h] ⟩ = 𝟙 A :=
  Limits.IsTerminal.hom_ext h _ (𝟙 A)
/-
**CategoryTheory.Endofunctor.Coalgebra.Terminal.right_inv** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Endofunctor.Coalgebra.Terminal`。
形式化陈述：right_inv : A.str ≫ strInv h = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Endofunctor.Coalgebra.Terminal.right_inv'`：right_inv' : ⟨
A.str ≫ strInv h, by rw [Category.assoc, F.map_comp, strInv, ← Hom.h] ⟩ = 𝟙 A
-/
theorem right_inv : A.str ≫ strInv h = 𝟙 _ :=
  congr_arg Hom.f (right_inv' h)
/-
**CategoryTheory.Endofunctor.Coalgebra.Terminal.left_inv** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Endofunctor.Coalgebra.Terminal`。
形式化陈述：left_inv : strInv h ≫ A.str = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Endofunctor.Coalgebra.Terminal.strInv.eq_1`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor C C}   {
A : CategoryTheory.Endofunctor.Coalgebra F} (h …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Endofunctor.Coalgebra.Hom.h`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {F : CategoryTheory.Functor C C}   {V₀ V₁ : Categor
yTheory.Endofunctor.Coalgebra F}…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Endofunctor.Coalgebra.Terminal.right_inv`：right_inv : A.s
tr ≫ strInv h = 𝟙 _
-/
theorem left_inv : strInv h ≫ A.str = 𝟙 _ := by
  rw [strInv, ← (h.from ⟨F.obj A.V, F.map A.str⟩).h, ← F.map_id, ← F.map_comp]
  congr
  exact right_inv h

/-- The structure map of the terminal coalgebra is an isomorphism,
hence endofunctors preserve their terminal coalgebras
-/
/-
**CategoryTheory.Endofunctor.Coalgebra.Terminal.str_isIso** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Endofunctor.Coalgebra.Terminal`。
形式化陈述：str_isIso (h : Limits.IsTerminal A) : IsIso A.str
参数：h : Limits.IsTerminal A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Endofunctor.Coalgebra.Terminal.right_inv`：right_inv : A.s
tr ≫ strInv h = 𝟙 _
· 使用定理 `CategoryTheory.Endofunctor.Coalgebra.Terminal.left_inv`：left_inv : strIn
v h ≫ A.str = 𝟙 _

--- 原说明 ---
The structure map of the terminal coalgebra is an isomorphism,
hence endofunctors preserve their terminal coalgebras
-/
theorem str_isIso (h : Limits.IsTerminal A) : IsIso A.str :=
  { out := ⟨strInv h, right_inv _, left_inv _⟩  }

end Terminal

end Coalgebra

namespace Adjunction

variable {F : C ⥤ C} {G : C ⥤ C}

/-
**CategoryTheory.Endofunctor.Adjunction.Algebra.homEquiv_naturality_str** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Endofunctor.Adjunction.Algebra`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F G : CategoryTh
eory.Functor C C} (adj : F ⊣ G)   (A₁ A₂ : CategoryTheory.Endofunctor.Algebra F)
 (f : A₁ ⟶ A₂),   CategoryTheory.CategoryStruct.comp ((adj.homEquiv A₁.a A₁.a) A
₁.str) (G.map f.f) =     CategoryTheory.CategoryStruct.comp f.f ((adj.homEquiv A
₂.a A₂.a) A₂.str)
参数：adj : F ⊣ G；A₁ A₂ : CategoryTheory.Endofunctor.Algebra F；f : A₁ ⟶ A₂；(adj.hom
Equiv A₁.a A₁.a) A₁.str；G.map f.f；(adj.homEquiv A₂.a A₂.a) A₂.str。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_right`：homEquiv_naturality
_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') : (adj.homEquiv X Y') (f ≫ g) = (adj.homEq
uiv X Y) f ≫ G.map g
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left`：homEquiv_naturality_
left (f : X' ⟶ X) (g : F.obj X ⟶ Y) : (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (a
dj.homEquiv X Y) g
· 使用定理 `CategoryTheory.Endofunctor.Algebra.Hom.h`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {F : CategoryTheory.Functor C C}   {A₀ A₁ : CategoryT
heory.Endofunctor.Algebra F} (…
-/
theorem Algebra.homEquiv_naturality_str (adj : F ⊣ G) (A₁ A₂ : Algebra F) (f : A₁ ⟶ A₂) :
    (adj.homEquiv A₁.a A₁.a) A₁.str ≫ G.map f.f = f.f ≫ (adj.homEquiv A₂.a A₂.a) A₂.str := by
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left, f.h]
/-
**CategoryTheory.Endofunctor.Adjunction.Coalgebra.homEquiv_naturality_str_symm**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Endofunctor.Adjunction.Coalgebra`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F G : CategoryTh
eory.Functor C C} (adj : F ⊣ G)   (V₁ V₂ : CategoryTheory.Endofunctor.Coalgebra 
G) (f : V₁ ⟶ V₂),   CategoryTheory.CategoryStruct.comp (F.map f.f) ((adj.homEqui
v V₂.V V₂.V).symm V₂.str) =     CategoryTheory.CategoryStruct.comp ((adj.homEqui
v V₁.V V₁.V).symm V₁.str) f.f
参数：adj : F ⊣ G；V₁ V₂ : CategoryTheory.Endofunctor.Coalgebra G；f : V₁ ⟶ V₂；F.map 
f.f；(adj.homEquiv V₂.V V₂.V).symm V₂.str；(adj.homEquiv V₁.V V₁.V).symm V₁.str。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left_symm`：homEquiv_natura
lity_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) : (adj.homEquiv X' Y).symm (f ≫ g)
 = F.map f ≫ (adj.homEquiv X Y).symm g
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_right_symm`：homEquiv_natur
ality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') : (adj.homEquiv X Y').symm (f ≫ 
G.map g) = (adj.homEquiv X Y).symm f ≫ g
· 使用定理 `CategoryTheory.Endofunctor.Coalgebra.Hom.h`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {F : CategoryTheory.Functor C C}   {V₀ V₁ : Categor
yTheory.Endofunctor.Coalgebra F}…
-/
theorem Coalgebra.homEquiv_naturality_str_symm (adj : F ⊣ G) (V₁ V₂ : Coalgebra G) (f : V₁ ⟶ V₂) :
    F.map f.f ≫ (adj.homEquiv V₂.V V₂.V).symm V₂.str =
    (adj.homEquiv V₁.V V₁.V).symm V₁.str ≫ f.f := by
  rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
    f.h]

/-- Given an adjunction `F ⊣ G`, the functor that associates to an algebra over `F` a
coalgebra over `G` defined via adjunction applied to the structure map. -/
@[simps!]
/-
**CategoryTheory.Endofunctor.Adjunction.Algebra.toCoalgebraOf** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Endofunctor.Adjunction.Algebra`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F G : Ca
tegoryTheory.Functor C C} →       (F ⊣ G) → CategoryTheory.Functor (CategoryTheo
ry.Endofunctor.Algebra F) (CategoryTheory.Endofunctor.Coalgebra G)
参数：F ⊣ G；CategoryTheory.Endofunctor.Algebra F；CategoryTheory.Endofunctor.Coalgeb
ra G。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Endofunctor.Adjunction.Algebra.homEquiv_naturality_str`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F G : CategoryTheory.Fu
nctor C C} (adj : F ⊣ G)   (A₁ A₂ : CategoryTheory.Endofunc…

--- 原说明 ---
Given an adjunction `F ⊣ G`, the functor that associates to an algebra over `F` 
a
coalgebra over `G` defined via adjunction applied to the structure map.
-/
def Algebra.toCoalgebraOf (adj : F ⊣ G) : Algebra F ⥤ Coalgebra G where
  obj A :=
    { V := A.1
      str := (adj.homEquiv A.1 A.1).toFun A.2 }
  map f :=
    { f := f.1
      h := Algebra.homEquiv_naturality_str adj _ _ f }

/-- Given an adjunction `F ⊣ G`, the functor that associates to a coalgebra over `G` an algebra over
`F` defined via adjunction applied to the structure map. -/
@[simps!]
/-
**CategoryTheory.Endofunctor.Adjunction.Coalgebra.toAlgebraOf** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Endofunctor.Adjunction.Coalgebra`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F G : Ca
tegoryTheory.Functor C C} →       (F ⊣ G) → CategoryTheory.Functor (CategoryTheo
ry.Endofunctor.Coalgebra G) (CategoryTheory.Endofunctor.Algebra F)
参数：F ⊣ G；CategoryTheory.Endofunctor.Coalgebra G；CategoryTheory.Endofunctor.Algeb
ra F。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Endofunctor.Adjunction.Coalgebra.homEquiv_naturality_str_
symm`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F G : CategoryTh
eory.Functor C C} (adj : F ⊣ G)   (V₁ V₂ : CategoryTheory.Endofunc…

--- 原说明 ---
Given an adjunction `F ⊣ G`, the functor that associates to a coalgebra over `G`
 an algebra over
`F` defined via adjunction applied to the structure map.
-/
def Coalgebra.toAlgebraOf (adj : F ⊣ G) : Coalgebra G ⥤ Algebra F where
  obj V :=
    { a := V.1
      str := (adj.homEquiv V.1 V.1).invFun V.2 }
  map f :=
    { f := f.1
      h := Coalgebra.homEquiv_naturality_str_symm adj _ _ f }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an adjunction, assigning to an algebra over the left adjoint a coalgebra over its right
adjoint and going back is isomorphic to the identity functor. -/
@[simps!]
/-
**CategoryTheory.Endofunctor.Adjunction.AlgCoalgEquiv.unitIso** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Endofunctor.Adjunction.AlgCoalgEquiv`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F G : Ca
tegoryTheory.Functor C C} →       (adj : F ⊣ G) →         CategoryTheory.Functor
.id (CategoryTheory.Endofunctor.Algebra F) ≅           (CategoryTheory.Endofunct
or.Adjunction.Algebra.toCoalgebraOf adj).comp             (CategoryTheory.Endofu
nctor.Adjunction.Coalgebra.toAlgebraOf adj)
参数：adj : F ⊣ G；CategoryTheory.Endofunctor.Algebra F；CategoryTheory.Endofunctor.A
djunction.Algebra.toCoalgebraOf adj；CategoryTheory.Endofunctor.Adjunction.Coalge
bra.toAlgebraOf adj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjunction, assigning to an algebra over the left adjoint a coalgebra o
ver its right
adjoint and going back is isomorphic to the identity functor.
-/
def AlgCoalgEquiv.unitIso (adj : F ⊣ G) :
    𝟭 (Algebra F) ≅ Algebra.toCoalgebraOf adj ⋙ Coalgebra.toAlgebraOf adj :=
  NatIso.ofComponents (fun _ ↦ Algebra.isoMk <| Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an adjunction, assigning to a coalgebra over the right adjoint an algebra over the left
adjoint and going back is isomorphic to the identity functor. -/
@[simps!]
/-
**CategoryTheory.Endofunctor.Adjunction.AlgCoalgEquiv.counitIso** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Endofunctor.Adjunction.AlgCoalgEquiv`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F G : Ca
tegoryTheory.Functor C C} →       (adj : F ⊣ G) →         (CategoryTheory.Endofu
nctor.Adjunction.Coalgebra.toAlgebraOf adj).comp             (CategoryTheory.End
ofunctor.Adjunction.Algebra.toCoalgebraOf adj) ≅           CategoryTheory.Functo
r.id (CategoryTheory.Endofunctor.Coalgebra G)
参数：adj : F ⊣ G；CategoryTheory.Endofunctor.Adjunction.Coalgebra.toAlgebraOf adj；C
ategoryTheory.Endofunctor.Adjunction.Algebra.toCoalgebraOf adj；CategoryTheory.En
dofunctor.Coalgebra G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjunction, assigning to a coalgebra over the right adjoint an algebra 
over the left
adjoint and going back is isomorphic to the identity functor.
-/
def AlgCoalgEquiv.counitIso (adj : F ⊣ G) :
    Coalgebra.toAlgebraOf adj ⋙ Algebra.toCoalgebraOf adj ≅ 𝟭 (Coalgebra G) :=
  NatIso.ofComponents (fun _ ↦ Coalgebra.isoMk <| Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- If `F` is left adjoint to `G`, then the category of algebras over `F` is equivalent to the
category of coalgebras over `G`. -/
@[simps!]
/-
**CategoryTheory.Endofunctor.Adjunction.algebraCoalgebraEquiv** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Endofunctor.Adjunction`。
形式化陈述：algebraCoalgebraEquiv (adj : F ⊣ G) : Algebra F ≌ Coalgebra G where functo
r
参数：adj : F ⊣ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is left adjoint to `G`, then the category of algebras over `F` is equival
ent to the
category of coalgebras over `G`.
-/
def algebraCoalgebraEquiv (adj : F ⊣ G) : Algebra F ≌ Coalgebra G where
  functor := Algebra.toCoalgebraOf adj
  inverse := Coalgebra.toAlgebraOf adj
  unitIso := AlgCoalgEquiv.unitIso adj
  counitIso := AlgCoalgEquiv.counitIso adj
  functor_unitIso_comp A := by
    ext
    simp

end Adjunction

end Endofunctor

end CategoryTheory

