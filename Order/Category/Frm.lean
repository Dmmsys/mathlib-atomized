/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.Lat
public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
# The category of frames

This file defines `Frm`, the category of frames.

## References

* [nLab, *Frm*](https://ncatlab.org/nlab/show/Frm)
-/

@[expose] public section


universe u

open CategoryTheory Order

/-- The category of frames. -/
/-
**Frm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of frames.
-/
structure Frm where
  /-- Construct a bundled `Frm` from the underlying type and typeclass. -/
  of ::
  /-- The underlying frame. -/
  (carrier : Type*)
  [str : Frame carrier]

attribute [instance] Frm.str

initialize_simps_projections Frm (carrier → coe, -str)

namespace Frm

/-
**Frm.** 是 Mathlib 中的一个实例，位于命名空间 `Frm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort Frm (Type _) :=
  ⟨Frm.carrier⟩

attribute [coe] Frm.carrier

/-- The type of morphisms in `Frm R`. -/
@[ext]
/-
**Frm.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Frm`。
形式化陈述：Frm → Frm → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `Frm R`.
-/
structure Hom (X Y : Frm.{u}) where
  private mk ::
  /-- The underlying `FrameHom`. -/
  hom' : FrameHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Frm.** 是 Mathlib 中的一个实例，位于命名空间 `Frm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category Frm.{u} where
  Hom X Y := Hom X Y
  id X := ⟨FrameHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Frm.** 是 Mathlib 中的一个实例，位于命名空间 `Frm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory Frm (FrameHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `Frm` back into a `FrameHom`. -/
/-
**Frm.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `Frm.Hom`。
形式化陈述：{X Y : Frm} → X.Hom Y → FrameHom ↑X ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `Frm` back into a `FrameHom`.
-/
abbrev Hom.hom {X Y : Frm.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Frm) f

/-- Typecheck a `FrameHom` as a morphism in `Frm`. -/
/-
**Frm.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Frm`。
形式化陈述：ofHom {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) : of X ⟶ of Y
参数：f : FrameHom X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `FrameHom` as a morphism in `Frm`.
-/
abbrev ofHom {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Frm) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**Frm.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `Frm.Hom.Simps`。
形式化陈述：(X Y : Frm) → X.Hom Y → FrameHom ↑X ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : Frm.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**Frm.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：coe_id {X : Frm} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : Frm} : (𝟙 X : X → X) = id := rfl

@[simp]
/-
**Frm.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：coe_comp {X Y Z : Frm} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : Frm} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
/-
**Frm.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：forget_map {X Y : Frm} (f : X ⟶ Y) : (forget Frm).map f = (f : _ -> _)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map {X Y : Frm} (f : X ⟶ Y) :
    (forget Frm).map f = (f : _ → _) := rfl

@[ext]
/-
**Frm.ext** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：ext {X Y : Frm} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : Frm} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/-
**Frm.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `Frm`。
形式化陈述：coe_of (X : Type u) [Frame X] : (Frm.of X : Type u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (X : Type u) [Frame X] : (Frm.of X : Type u) = X := rfl

@[simp]
/-
**Frm.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：hom_id {X : Frm} : (𝟙 X : X ⟶ X).hom = FrameHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : Frm} : (𝟙 X : X ⟶ X).hom = FrameHom.id _ := rfl

/- Provided for rewriting. -/
/-
**Frm.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：id_apply (X : Frm) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : Frm；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (X : Frm) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**Frm.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：hom_comp {X Y Z : Frm} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.hom.comp 
f.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : Frm} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**Frm.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：comp_apply {X Y Z : Frm} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (
f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y Z : Frm} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**Frm.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：hom_ext {X Y : Frm} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Frm.Hom.ext`：∀ {X Y : Frm} {x y : X.Hom Y}, x.hom' = y.hom' → x = y
-/
lemma hom_ext {X Y : Frm} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**Frm.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：hom_ofHom {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) : (ofHom f
).hom = f
参数：f : FrameHom X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) : (ofHom f).hom = f := rfl

@[simp]
/-
**Frm.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：ofHom_hom {X Y : Frm} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : Frm} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**Frm.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：ofHom_id {X : Type u} [Frame X] : ofHom (FrameHom.id _) = 𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [Frame X] : ofHom (FrameHom.id _) = 𝟙 (of X) := rfl

@[simp]
/-
**Frm.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：ofHom_comp {X Y Z : Type u} [Frame X] [Frame Y] [Frame Z] (f : FrameHom X 
Y) (g : FrameHom Y Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : FrameHom X Y；g : FrameHom Y Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [Frame X] [Frame Y] [Frame Z]
    (f : FrameHom X Y) (g : FrameHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**Frm.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：ofHom_apply {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) (x : X) 
: (ofHom f) x = f x
参数：f : FrameHom X Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) (x : X) :
    (ofHom f) x = f x := rfl
/-
**Frm.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：inv_hom_apply {X Y : Frm} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x
参数：e : X ≅ Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_hom_apply {X Y : Frm} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp
/-
**Frm.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Frm`。
形式化陈述：hom_inv_apply {X Y : Frm} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s
参数：e : X ≅ Y；s : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_inv_apply {X Y : Frm} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp
/-
**Frm.** 是 Mathlib 中的一个实例，位于命名空间 `Frm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Frm :=
  ⟨of PUnit⟩
/-
**Frm.hasForgetToLat** 是 Mathlib 中的一个实例，位于命名空间 `Frm`。
形式化陈述：hasForgetToLat : HasForget₂ Frm Lat where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToLat : HasForget₂ Frm Lat where
  forget₂.obj X := .of X
  forget₂.map f := Lat.ofHom f.hom

/-- Constructs an isomorphism of frames from an order isomorphism between them. -/
@[simps]
/-
**Frm.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `Frm.Iso`。
形式化陈述：{α β : Frm} → ↑α ≃o ↑β → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an isomorphism of frames from an order isomorphism between them.
-/
def Iso.mk {α β : Frm.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

end Frm

