/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# `eqToHom` in bicategories

This file records some of the behavior of `eqToHom` 1-morphisms and
2-morphisms in bicategories.

Given an equality of objects `h : x = y` in a bicategory, there is a 1-morphism
`eqToHom h : x ⟶ y` just like in an ordinary category. The definitional property
of this morphism is that if `h : x = x`, `eqToHom h = 𝟙 x`. This is
implemented as the `eqToHom` morphism in the `CategoryStruct` underlying the
bicategory.

Unlike the situation in ordinary category theory, these 1-morphisms do not
compose strictly: `eqToHom h.trans h'` is merely isomorphic to
`eqToHom h ≫ eqToHom h'`. We define this isomorphism as
`CategoryTheory.Bicategory.eqToHomTransIso`.

Given an equality of 1-morphisms, we show that various bicategorical
structure morphisms such as unitors, associators and whiskering conjugate
well under `eqToHom`s.

## TODO
* Define `eqToEquiv` that puts the `eqToHom`s in an `Equivalence` between
  objects.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- In a bicategory, `eqToHom`s do not compose strictly,
but they do up to isomorphism. -/
/-
**CategoryTheory.Bicategory.eqToHomTransIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Bicategory`。
形式化陈述：eqToHomTransIso {x y z : B} (e₁ : x = y) (e₂ : y = z) : eqToHom (e₁.trans 
e₂) ≅ eqToHom e₁ ≫ eqToHom e₂
参数：e₁ : x = y；e₂ : y = z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
In a bicategory, `eqToHom`s do not compose strictly,
but they do up to isomorphism.
-/
def eqToHomTransIso {x y z : B} (e₁ : x = y) (e₂ : y = z) :
    eqToHom (e₁.trans e₂) ≅ eqToHom e₁ ≫ eqToHom e₂ :=
  e₂ ▸ e₁ ▸ (λ_ (𝟙 x)).symm

@[simp]
/-
**CategoryTheory.Bicategory.eqToHomTransIso_refl_refl** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Bicategory`。
形式化陈述：eqToHomTransIso_refl_refl (x : B) : eqToHomTransIso (rfl : x = x) rfl = (f
un_ (𝟙 x)).symm
参数：x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma eqToHomTransIso_refl_refl (x : B) :
    eqToHomTransIso (rfl : x = x) rfl = (λ_ (𝟙 x)).symm :=
  rfl
/-
**CategoryTheory.Bicategory.eqToHomTransIso_refl_right** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Bicategory`。
形式化陈述：eqToHomTransIso_refl_right {x y : B} (e₁ : x = y) : eqToHomTransIso e₁ rfl
 = (ρ_ (eqToHom e₁)).symm
参数：e₁ : x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.unitors_inv_equal`：unitors_inv_equal : (fun_ (
𝟙 a)).inv = (ρ_ (𝟙 a)).inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eqToHomTransIso_refl_right {x y : B} (e₁ : x = y) :
    eqToHomTransIso e₁ rfl = (ρ_ (eqToHom e₁)).symm := by
  ext
  subst e₁
  simp
/-
**CategoryTheory.Bicategory.eqToHomTransIso_refl_left** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Bicategory`。
形式化陈述：eqToHomTransIso_refl_left {x y : B} (e₁ : x = y) : eqToHomTransIso rfl e₁ 
= (fun_ (eqToHom e₁)).symm
参数：e₁ : x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.unitors_inv_equal`：unitors_inv_equal : (fun_ (
𝟙 a)).inv = (ρ_ (𝟙 a)).inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eqToHomTransIso_refl_left {x y : B} (e₁ : x = y) :
    eqToHomTransIso rfl e₁ = (λ_ (eqToHom e₁)).symm := by
  ext
  subst e₁
  simp

@[reassoc]
/-
**CategoryTheory.Bicategory.associator_eqToHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Bicategory`。
形式化陈述：associator_eqToHom_hom {x y z t : B} (e₁ : x = y) (e₂ : y = z) (e₃ : z = t
) : (α_ (eqToHom e₁) (eqToHom e₂) (eqToHom e₃)).hom = (eqToHomTransIso e₁ e₂).in
v ▷ eqToHom e₃ ≫ (eqToHomTransIso (e₁.trans e₂) e₃).inv ≫ (eqToHomTransIso e₁ (e
₂.trans e₃)).hom ≫ eqToHom e₁ ◁ (eqToHomTransIso e₂ e₃).hom
参数：e₁ : x = y；e₂ : y = z；e₃ : z = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Bicategory.unitors_equal`：unitors_equal : (fun_ (𝟙 a)).ho
m = (ρ_ (𝟙 a)).hom
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_id`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bic
ategory.whiskerRight η (Categor…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Bicategory.unitors_inv_equal`：unitors_inv_equal : (fun_ (
𝟙 a)).inv = (ρ_ (𝟙 a)).inv
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_rightUnitor_inv`：whiskerLeft_right
Unitor_inv (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).inv = (ρ_ (f ≫ g)).inv ≫ (α_ f g
 (𝟙 c)).hom
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_eqToHom_hom {x y z t : B}
    (e₁ : x = y) (e₂ : y = z) (e₃ : z = t) :
    (α_ (eqToHom e₁) (eqToHom e₂) (eqToHom e₃)).hom =
    (eqToHomTransIso e₁ e₂).inv ▷ eqToHom e₃ ≫
      (eqToHomTransIso (e₁.trans e₂) e₃).inv ≫
      (eqToHomTransIso e₁ (e₂.trans e₃)).hom ≫
      eqToHom e₁ ◁ (eqToHomTransIso e₂ e₃).hom := by
  subst_vars
  simp

@[reassoc]
/-
**CategoryTheory.Bicategory.associator_eqToHom_inv** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Bicategory`。
形式化陈述：associator_eqToHom_inv {x y z t : B} (e₁ : x = y) (e₂ : y = z) (e₃ : z = t
) : (α_ (eqToHom e₁) (eqToHom e₂) (eqToHom e₃)).inv = eqToHom e₁ ◁ (eqToHomTrans
Iso e₂ e₃).inv ≫ (eqToHomTransIso e₁ (e₂.trans e₃)).inv ≫ (eqToHomTransIso (e₁.t
rans e₂) e₃).hom ≫ (eqToHomTransIso e₁ e₂).hom ▷ eqToHom e₃
参数：e₁ : x = y；e₂ : y = z；e₃ : z = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.unitors_equal`：unitors_equal : (fun_ (𝟙 a)).ho
m = (ρ_ (𝟙 a)).hom
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_rightUnitor`：whiskerLeft_rightUnit
or (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).hom = (α_ f g (𝟙 c)).inv ≫ (ρ_ (f ≫ g)).
hom
· 使用定理 `CategoryTheory.Bicategory.unitors_inv_equal`：unitors_inv_equal : (fun_ (
𝟙 a)).inv = (ρ_ (𝟙 a)).inv
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_id`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bic
ategory.whiskerRight η (Categor…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_eqToHom_inv {x y z t : B}
    (e₁ : x = y) (e₂ : y = z) (e₃ : z = t) :
    (α_ (eqToHom e₁) (eqToHom e₂) (eqToHom e₃)).inv =
    eqToHom e₁ ◁ (eqToHomTransIso e₂ e₃).inv ≫
      (eqToHomTransIso e₁ (e₂.trans e₃)).inv ≫
      (eqToHomTransIso (e₁.trans e₂) e₃).hom ≫
      (eqToHomTransIso e₁ e₂).hom ▷ eqToHom e₃ := by
  subst_vars
  simp
/-
**CategoryTheory.Bicategory.associator_hom_congr** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：associator_hom_congr {x y z t : B} {f f' : x ⟶ y} {g g' : y ⟶ z} {h h' : z
 ⟶ t} (ef : f = f') (eg : g = g') (eh : h = h') : (α_ f g h).hom = eqToHom (by g
rind) ≫ (α_ f' g' h').hom ≫ eqToHom (by grind)
参数：ef : f = f'；eg : g = g'；eh : h = h'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_hom_congr {x y z t : B} {f f' : x ⟶ y} {g g' : y ⟶ z}
    {h h' : z ⟶ t} (ef : f = f') (eg : g = g') (eh : h = h') :
    (α_ f g h).hom =
    eqToHom (by grind) ≫ (α_ f' g' h').hom ≫ eqToHom (by grind) := by
  subst_vars
  simp
/-
**CategoryTheory.Bicategory.associator_inv_congr** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：associator_inv_congr {x y z t : B} {f f' : x ⟶ y} {g g' : y ⟶ z} {h h' : z
 ⟶ t} (ef : f = f') (eg : g = g') (eh : h = h') : (α_ f g h).inv = eqToHom (by g
rind) ≫ (α_ f' g' h').inv ≫ eqToHom (by grind)
参数：ef : f = f'；eg : g = g'；eh : h = h'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_inv_congr {x y z t : B} {f f' : x ⟶ y} {g g' : y ⟶ z}
    {h h' : z ⟶ t} (ef : f = f') (eg : g = g') (eh : h = h') :
    (α_ f g h).inv =
    eqToHom (by grind) ≫ (α_ f' g' h').inv ≫ eqToHom (by grind) := by
  subst_vars
  simp
/-
**CategoryTheory.Bicategory.congr_whiskerLeft** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Bicategory`。
形式化陈述：congr_whiskerLeft {x y : B} {f f' : x ⟶ y} (h : f = f') {z : B} {g g' : y 
⟶ z} (η : g ⟶ g') : f ◁ η = eqToHom (by rw [h]) ≫ f' ◁ η ≫ eqToHom (by rw [h])
参数：h : f = f'；η : g ⟶ g'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma congr_whiskerLeft {x y : B} {f f' : x ⟶ y} (h : f = f') {z : B}
    {g g' : y ⟶ z} (η : g ⟶ g') :
      f ◁ η = eqToHom (by rw [h]) ≫ f' ◁ η ≫ eqToHom (by rw [h]) := by
  subst h
  simp
/-
**CategoryTheory.Bicategory.whiskerRight_congr** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Bicategory`。
形式化陈述：whiskerRight_congr {y z : B} {g g' : y ⟶ z} (h : g = g') {x : B} {f f' : x
 ⟶ y} (η : f ⟶ f') : η ▷ g = eqToHom (by rw [h]) ≫ η ▷ g' ≫ eqToHom (by rw [h])
参数：h : g = g'；η : f ⟶ f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerRight_congr {y z : B} {g g' : y ⟶ z} (h : g = g') {x : B}
    {f f' : x ⟶ y} (η : f ⟶ f') :
      η ▷ g = eqToHom (by rw [h]) ≫ η ▷ g' ≫ eqToHom (by rw [h]) := by
  subst h
  simp
/-
**CategoryTheory.Bicategory.leftUnitor_hom_congr** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：leftUnitor_hom_congr {x y : B} {f f' : x ⟶ y} (h : f = f') : (fun_ f).hom 
= 𝟙 _ ◁ (eqToHom h) ≫ (fun_ f').hom ≫ eqToHom h.symm
参数：h : f = f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_id`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bica
tegory.whiskerLeft f (Category…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftUnitor_hom_congr {x y : B} {f f' : x ⟶ y} (h : f = f') :
    (λ_ f).hom = 𝟙 _ ◁ (eqToHom h) ≫ (λ_ f').hom ≫ eqToHom h.symm := by
  subst h
  simp
/-
**CategoryTheory.Bicategory.leftUnitor_inv_congr** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：leftUnitor_inv_congr {x y : B} {f f' : x ⟶ y} (h : f = f') : (fun_ f).inv 
= (eqToHom h) ≫ (fun_ f').inv ≫ 𝟙 _ ◁ eqToHom h.symm
参数：h : f = f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_id`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bica
tegory.whiskerLeft f (Category…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftUnitor_inv_congr {x y : B} {f f' : x ⟶ y} (h : f = f') :
    (λ_ f).inv = (eqToHom h) ≫ (λ_ f').inv ≫ 𝟙 _ ◁ eqToHom h.symm := by
  subst h
  simp
/-
**CategoryTheory.Bicategory.rightUnitor_hom_congr** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Bicategory`。
形式化陈述：rightUnitor_hom_congr {x y : B} {f f' : x ⟶ y} (h : f = f') : (ρ_ f).hom =
 (eqToHom h) ▷ 𝟙 _ ≫ (ρ_ f').hom ≫ eqToHom h.symm
参数：h : f = f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_id`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bic
ategory.whiskerRight η (Categor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightUnitor_hom_congr {x y : B} {f f' : x ⟶ y} (h : f = f') :
    (ρ_ f).hom = (eqToHom h) ▷ 𝟙 _ ≫ (ρ_ f').hom ≫ eqToHom h.symm := by
  subst h
  simp
/-
**CategoryTheory.Bicategory.rightUnitor_inv_congr** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Bicategory`。
形式化陈述：rightUnitor_inv_congr {x y : B} {f f' : x ⟶ y} (h : f = f') : (ρ_ f).inv =
 (eqToHom h) ≫ (ρ_ f').inv ≫ eqToHom h.symm ▷ 𝟙 _
参数：h : f = f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_id`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bic
ategory.whiskerRight η (Categor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightUnitor_inv_congr {x y : B} {f f' : x ⟶ y} (h : f = f') :
    (ρ_ f).inv = (eqToHom h) ≫ (ρ_ f').inv ≫ eqToHom h.symm ▷ 𝟙 _ := by
  subst h
  simp

end CategoryTheory.Bicategory

