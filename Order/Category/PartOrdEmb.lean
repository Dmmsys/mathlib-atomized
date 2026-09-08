/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
module

public import Mathlib.Order.Category.PartOrd
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Category of partial orders, with order embeddings as morphisms

This defines `PartOrdEmb`, the category of partial orders with order embeddings
as morphisms. We also show that `PartOrdEmb` has filtered colimits.

-/

@[expose] public section

open CategoryTheory Limits

universe u

/-- The category of partial orders. -/
/-
**PartOrdEmb** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of partial orders.
-/
structure PartOrdEmb where
  /-- Construct a bundled `PartOrdEmb` from the underlying type and typeclass. -/
  of ::
  /-- The underlying partially ordered type. -/
  (carrier : Type*)
  [str : PartialOrder carrier]

attribute [instance] PartOrdEmb.str

initialize_simps_projections PartOrdEmb (carrier → coe, -str)

namespace PartOrdEmb

/-
**PartOrdEmb.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort PartOrdEmb (Type _) :=
  ⟨PartOrdEmb.carrier⟩

attribute [coe] PartOrdEmb.carrier

/-- The type of morphisms in `PartOrdEmb R`. -/
@[ext]
/-
**PartOrdEmb.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `PartOrdEmb`。
形式化陈述：PartOrdEmb → PartOrdEmb → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `PartOrdEmb R`.
-/
structure Hom (X Y : PartOrdEmb.{u}) where
  private mk ::
  /-- The underlying `OrderEmbedding`. -/
  hom' : X ↪o Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**PartOrdEmb.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category PartOrdEmb.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨RelEmbedding.refl _⟩
  comp f g := ⟨f.hom'.trans g.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**PartOrdEmb.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory PartOrdEmb (· ↪o ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `PartOrdEmb` back into a `OrderEmbedding`. -/
/-
**PartOrdEmb.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb.Hom`。
形式化陈述：{X Y : PartOrdEmb} → X.Hom Y → ↑X ↪o ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `PartOrdEmb` back into a `OrderEmbedding`.
-/
abbrev Hom.hom {X Y : PartOrdEmb.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := PartOrdEmb) f

/-- Typecheck a `OrderEmbedding` as a morphism in `PartOrdEmb`. -/
/-
**PartOrdEmb.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `PartOrdEmb`。
形式化陈述：ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) : of X
 ⟶ of Y
参数：f : X ↪o Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `OrderEmbedding` as a morphism in `PartOrdEmb`.
-/
abbrev ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := PartOrdEmb) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**PartOrdEmb.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb.Hom.Simps`。
形式化陈述：(X Y : PartOrdEmb) → X.Hom Y → ↑X ↪o ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : PartOrdEmb.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**PartOrdEmb.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：coe_id {X : PartOrdEmb} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : PartOrdEmb} : (𝟙 X : X → X) = id := rfl

@[simp]
/-
**PartOrdEmb.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：coe_comp {X Y Z : PartOrdEmb} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) =
 g ∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : PartOrdEmb} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
/-
**PartOrdEmb.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：forget_map {X Y : PartOrdEmb} (f : X ⟶ Y) : (forget PartOrdEmb).map f = (f
 : _ -> _)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map {X Y : PartOrdEmb} (f : X ⟶ Y) :
    (forget PartOrdEmb).map f = (f : _ → _) := rfl

@[ext]
/-
**PartOrdEmb.ext** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：ext {X Y : PartOrdEmb} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : PartOrdEmb} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/-
**PartOrdEmb.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `PartOrdEmb`。
形式化陈述：coe_of (X : Type u) [PartialOrder X] : (PartOrdEmb.of X : Type u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (X : Type u) [PartialOrder X] : (PartOrdEmb.of X : Type u) = X := rfl
/-
**PartOrdEmb.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：hom_id {X : PartOrdEmb} : (𝟙 X : X ⟶ X).hom = RelEmbedding.refl _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : PartOrdEmb} : (𝟙 X : X ⟶ X).hom = RelEmbedding.refl _ := rfl

/- Provided for rewriting. -/
/-
**PartOrdEmb.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：id_apply (X : PartOrdEmb) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : PartOrdEmb；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (X : PartOrdEmb) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**PartOrdEmb.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：hom_comp {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.ho
m.trans g.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom.trans g.hom := rfl

/- Provided for rewriting. -/
/-
**PartOrdEmb.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：comp_apply {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) 
x = g (f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp
/-
**PartOrdEmb.Hom.injective** 是 Mathlib 中的一个定理，位于命名空间 `PartOrdEmb.Hom`。
形式化陈述：∀ {X Y : PartOrdEmb} (f : X ⟶ Y), Function.Injective ⇑(CategoryTheory.Conc
reteCategory.hom f)
参数：f : X ⟶ Y；CategoryTheory.ConcreteCategory.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
lemma Hom.injective {X Y : PartOrdEmb.{u}} (f : X ⟶ Y) : Function.Injective f :=
  f.hom'.injective
/-
**PartOrdEmb.Hom.le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `PartOrdEmb.Hom`。
形式化陈述：∀ {X Y : PartOrdEmb} (f : X ⟶ Y) (x₁ x₂ : ↑X),   (CategoryTheory.ConcreteC
ategory.hom f) x₁ ≤ (CategoryTheory.ConcreteCategory.hom f) x₂ ↔ x₁ ≤ x₂
参数：f : X ⟶ Y；x₁ x₂ : ↑X；CategoryTheory.ConcreteCategory.hom f；CategoryTheory.Con
creteCategory.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
lemma Hom.le_iff_le {X Y : PartOrdEmb.{u}} (f : X ⟶ Y) (x₁ x₂ : X) :
    f x₁ ≤ f x₂ ↔ x₁ ≤ x₂ :=
  f.hom'.le_iff_le

@[ext]
/-
**PartOrdEmb.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：hom_ext {X Y : PartOrdEmb} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartOrdEmb.Hom.ext`：∀ {X Y : PartOrdEmb} {x y : X.Hom Y}, x.hom' = y.hom
' → x = y
-/
lemma hom_ext {X Y : PartOrdEmb} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**PartOrdEmb.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：hom_ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) : 
(ofHom f).hom = f
参数：f : X ↪o Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) :
    (ofHom f).hom = f :=
  rfl

@[simp]
/-
**PartOrdEmb.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：ofHom_hom {X Y : PartOrdEmb} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : PartOrdEmb} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**PartOrdEmb.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：ofHom_id {X : Type u} [PartialOrder X] : ofHom (RelEmbedding.refl _) = 𝟙 (
of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [PartialOrder X] : ofHom (RelEmbedding.refl _) = 𝟙 (of X) := rfl

@[simp]
/-
**PartOrdEmb.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：ofHom_comp {X Y Z : Type u} [PartialOrder X] [PartialOrder Y] [PartialOrde
r Z] (f : X ↪o Y) (g : Y ↪o Z) : ofHom (f.trans g) = ofHom f ≫ ofHom g
参数：f : X ↪o Y；g : Y ↪o Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]
    (f : X ↪o Y) (g : Y ↪o Z) :
    ofHom (f.trans g) = ofHom f ≫ ofHom g :=
  rfl
/-
**PartOrdEmb.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：ofHom_apply {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) 
(x : X) : (ofHom f) x = f x
参数：f : X ↪o Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) (x : X) :
    (ofHom f) x = f x := rfl
/-
**PartOrdEmb.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：inv_hom_apply {X Y : PartOrdEmb} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x
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
lemma inv_hom_apply {X Y : PartOrdEmb} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp
/-
**PartOrdEmb.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：hom_inv_apply {X Y : PartOrdEmb} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s
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
lemma hom_inv_apply {X Y : PartOrdEmb} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp
/-
**PartOrdEmb.hasForgetToPartOrd** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb`。
形式化陈述：hasForgetToPartOrd : HasForget₂ PartOrdEmb PartOrd where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToPartOrd : HasForget₂ PartOrdEmb PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom f.hom

/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps]
/-
**PartOrdEmb.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb.Iso`。
形式化陈述：{α β : PartOrdEmb} → ↑α ≃o ↑β → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an equivalence between partial orders from an order isomorphism betwe
en them.
-/
def Iso.mk {α β : PartOrdEmb.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- The order isomorphism corresponding to an isomorphism in `PartOrdEmb`. -/
@[simps]
/-
**PartOrdEmb.orderIsoOfIso** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb`。
形式化陈述：orderIsoOfIso {α β : PartOrdEmb.{u}} (e : α ≅ β) : α ≃o β where toFun
参数：e : α ≅ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order isomorphism corresponding to an isomorphism in `PartOrdEmb`.
-/
def orderIsoOfIso {α β : PartOrdEmb.{u}} (e : α ≅ β) :
    α ≃o β where
  toFun := e.hom
  invFun := e.inv
  left_inv := ConcreteCategory.congr_hom e.hom_inv_id
  right_inv := ConcreteCategory.congr_hom e.inv_hom_id
  map_rel_iff' := Hom.le_iff_le _ _ _

/-- Isomorphisms in `PartOrdEmb` correspond to order isomorphisms. -/
@[simps]
/-
**PartOrdEmb.orderIsoEquivIso** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb`。
形式化陈述：orderIsoEquivIso {α β : PartOrdEmb.{u}} : (α ≅ β) ≃ (α ≃o β) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphisms in `PartOrdEmb` correspond to order isomorphisms.
-/
def orderIsoEquivIso {α β : PartOrdEmb.{u}} :
    (α ≅ β) ≃ (α ≃o β) where
  toFun := orderIsoOfIso
  invFun := Iso.mk
/-
**PartOrdEmb.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget PartOrdEmb.{u}).ReflectsIsomorphisms where
  reflects {α β} f hf := by
    rw [CategoryTheory.isIso_iff_bijective] at hf
    let e : α ≃o β :=
      { toEquiv := Equiv.ofBijective _ hf
        map_rel_iff' := by simp }
    exact (Iso.mk e).isIso_hom

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**PartOrdEmb.dual** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb`。
形式化陈述：dual : PartOrdEmb ⥤ PartOrdEmb where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : PartOrdEmb ⥤ PartOrdEmb where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `PartOrdEmb` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**PartOrdEmb.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb`。
形式化陈述：dualEquiv : PartOrdEmb ≌ PartOrdEmb where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `PartOrdEmb` and itself induced by `OrderDual` both ways
.
-/
def dualEquiv : PartOrdEmb ≌ PartOrdEmb where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end PartOrdEmb

/-
**partOrdEmb_dual_comp_forget_to_pardOrd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partOrdEmb_dual_comp_forget_to_pardOrd : PartOrdEmb.dual ⋙ forget₂ PartOrd
Emb PartOrd = forget₂ PartOrdEmb PartOrd ⋙ PartOrd.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem partOrdEmb_dual_comp_forget_to_pardOrd :
    PartOrdEmb.dual ⋙ forget₂ PartOrdEmb PartOrd =
      forget₂ PartOrdEmb PartOrd ⋙ PartOrd.dual :=
  rfl

namespace PartOrdEmb

namespace Limits

variable {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ PartOrdEmb.{u}}
  {c : Cocone (F ⋙ forget _)} (hc : IsColimit c)

/-- Given a functor `F : J ⥤ PartOrdEmb` and a colimit cocone `c` for
`F ⋙ forget _`, this is the type `c.pt` on which we define a partial order
which makes it the colimit of `F`. -/
@[nolint unusedArguments]
/-
**PartOrdEmb.Limits.CoconePt** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb.Limits`。
形式化陈述：CoconePt (_ : IsColimit c) : Type u
参数：_ : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : J ⥤ PartOrdEmb` and a colimit cocone `c` for
`F ⋙ forget _`, this is the type `c.pt` on which we define a partial order
which makes it the colimit of `F`.
-/
def CoconePt (_ : IsColimit c) : Type u := c.pt

open IsFiltered
/-
**PartOrdEmb.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (CoconePt hc) where
  le x y := ∃ (j : J) (x' y' : F.obj j) (hx : c.ι.app j x' = x)
      (hy : c.ι.app j y' = y), x' ≤ y'
  le_refl x := by
    obtain ⟨j, x', hx⟩ := Types.jointly_surjective_of_isColimit hc x
    exact ⟨j, x', x', hx, hx, le_rfl⟩
  le_trans := by
    rintro x y z ⟨j, x₁, y₁, hx₁, hy₁, hxy⟩ ⟨k, y₂, z₁, hy₂, hz₁, hyz⟩
    obtain ⟨l, a, b, h⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff _ hc (xi := y₁) (xj := y₂)).1
        (hy₁.trans hy₂.symm)
    exact ⟨l, F.map a x₁, F.map b z₁,
      (ConcreteCategory.congr_hom (c.w a) x₁).trans hx₁,
      (ConcreteCategory.congr_hom (c.w b) z₁).trans hz₁,
      ((F.map a).hom.monotone hxy).trans
        (le_of_eq_of_le h ((F.map b).hom.monotone hyz))⟩
  le_antisymm := by
    rintro x y ⟨j, x₁, y₁, hx₁, hy₁, h₁⟩ ⟨k, y₂, x₂, hy₂, hx₂, h₂⟩
    obtain ⟨l, a, b, x₃, y₃, h₃, h₄, h₅, h₆⟩ :
        ∃ (l : J) (a : j ⟶ l) (b : k ⟶ l) (x₃ y₃ : _),
        x₃ = F.map a x₁ ∧ x₃ = F.map b x₂ ∧ y₃ = F.map a y₁ ∧ y₃ = F.map b y₂ := by
      obtain ⟨l₁, a, b, h₃⟩ :=
        (Types.FilteredColimit.isColimit_eq_iff _ hc (xi := x₁) (xj := x₂)).1
          (hx₁.trans hx₂.symm)
      obtain ⟨l₂, a', b', h₄⟩ :=
        (Types.FilteredColimit.isColimit_eq_iff _ hc (xi := y₁) (xj := y₂)).1
          (hy₁.trans hy₂.symm)
      obtain ⟨l, d, d', h₅, h₆⟩ := IsFiltered.bowtie a a' b b'
      exact ⟨l, a ≫ d, b ≫ d, F.map (a ≫ d) x₁, F.map (a' ≫ d') y₁, rfl,
        by simpa, by rw [h₅], by simpa [h₆]⟩
    have h₇ : x₃ = y₃ :=
      le_antisymm
        (by simpa only [h₃, h₅] using (F.map a).hom.monotone h₁)
        (by simpa only [h₄, h₆] using (F.map b).hom.monotone h₂)
    exact hx₁.symm.trans ((ConcreteCategory.congr_hom (c.w a) x₁).symm.trans
      ((congr_arg (c.ι.app l) (h₃.symm.trans (h₇.trans h₅))).trans
        ((ConcreteCategory.congr_hom (c.w a) y₁).trans hy₁)))

/-- The colimit cocone for a functor `F : J ⥤ PartOrdEmb` from a filtered
category that is constructed from a colimit cocone for `F ⋙ forget _`. -/
@[simps]
/-
**PartOrdEmb.Limits.cocone** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb.Limits`。
形式化陈述：cocone : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cocone for a functor `F : J ⥤ PartOrdEmb` from a filtered
category that is constructed from a colimit cocone for `F ⋙ forget _`.
-/
def cocone : Cocone F where
  pt := .of (CoconePt hc)
  ι.app j := ofHom
    { toFun := c.ι.app j
      inj' x y h := by
        obtain ⟨k, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc x y).1 h
        exact (F.map a).injective ha
      map_rel_iff' {x y} := by
        refine ⟨?_, fun h ↦ ⟨j, x, y, rfl, rfl, h⟩⟩
        rintro ⟨k, x', y', hx, hy, h⟩
        obtain ⟨l₁, a₁, b₁, hl₁⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc).1 hx
        obtain ⟨l₂, a₂, b₂, hl₂⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc).1 hy
        dsimp at hx hy hl₁ hl₂
        obtain ⟨m, d, d', h₁, h₂⟩ := bowtie a₁ a₂ b₁ b₂
        rw [← (F.map (a₁ ≫ d)).le_iff_le] at h
        rw [← (F.map (b₁ ≫ d)).le_iff_le]
        conv_rhs => rw [h₂]
        conv_rhs at h => rw [h₁]
        simpa [← hl₁, ← hl₂] using h }
  ι.naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (c.w f) x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `isColimitCocone`. -/
/-
**PartOrdEmb.Limits.CoconePt.desc** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb.Limits.C
oconePt`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.SmallCategory J] →     [inst_1 : C
ategoryTheory.IsFiltered J] →       {F : CategoryTheory.Functor J PartOrdEmb} → 
        {c : CategoryTheory.Limits.Cocone (F.comp (CategoryTheory.forget PartOrd
Emb))} →           (hc : CategoryTheory.Limits.IsColimit c) →             (s : C
ategoryTheory.Limits.Cocone F) → PartOrdEmb.Limits.CoconePt hc ↪o ↑s.pt
参数：F.comp (CategoryTheory.forget PartOrdEmb)；hc : CategoryTheory.Limits.IsColimi
t c；s : CategoryTheory.Limits.Cocone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `isColimitCocone`.
-/
def CoconePt.desc (s : Cocone F) : CoconePt hc ↪o s.pt where
  toFun := hc.desc ((forget _).mapCocone s)
  inj' x y h := by
    obtain ⟨j, x', y', rfl, rfl⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ hc x y
    obtain rfl := (s.ι.app j).injective
      (((ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x').symm.trans h).trans
        (ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) y'))
    rfl
  map_rel_iff' {x y} := by
    obtain ⟨j, x', y', rfl, rfl⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ hc x y
    have hx := ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x'
    have hy := ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) y'
    simp only [Functor.mapCocone_pt, Functor.comp_obj, Functor.const_obj_obj,
      CategoryTheory.comp_apply, Functor.mapCocone_ι_app, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk, Function.Embedding.coeFn_mk] at hx hy ⊢
    rw [hx, hy, OrderEmbedding.le_iff_le]
    refine ⟨fun h ↦ ⟨j, _, _, rfl, rfl, h⟩, fun ⟨k, x, y, hx', hy', h⟩ ↦ ?_⟩
    obtain ⟨l, f, g, hl⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc).1 hx'
    obtain ⟨l', f', g', hl'⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc).1 hy'
    obtain ⟨m, a, b, h₁, h₂⟩ := bowtie f f' g g'
    dsimp at hl hl'
    rw [← (F.map (f ≫ a)).le_iff_le] at h
    rw [← (F.map (g ≫ a)).le_iff_le]
    exact le_of_eq_of_le (by simp [hl]) (le_of_le_of_eq h (by simp [h₁, h₂, hl']))

@[simp]
/-
**PartOrdEmb.Limits.CoconePt.fac_apply** 是 Mathlib 中的一个定理，位于命名空间 `PartOrdEmb.Lim
its.CoconePt`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.SmallCategory J] [inst_1 : CategoryT
heory.IsFiltered J]   {F : CategoryTheory.Functor J PartOrdEmb}   {c : CategoryT
heory.Limits.Cocone (F.comp (CategoryTheory.forget PartOrdEmb))}   (hc : Categor
yTheory.Limits.IsColimit c) (s : CategoryTheory.Limits.Cocone F) (j : J) (x : ↑(
F.obj j)),   (PartOrdEmb.Limits.CoconePt.desc hc s) ((CategoryTheory.ConcreteCat
egory.hom (c.ι.app j)) x) =     (CategoryTheory.ConcreteCategory.hom (s.ι.app j)
) x
参数：F.comp (CategoryTheory.forget PartOrdEmb)；hc : CategoryTheory.Limits.IsColimi
t c；s : CategoryTheory.Limits.Cocone F；j : J；x : ↑(F.obj j)；PartOrdEmb.Limits.Co
conePt.desc hc s；(CategoryTheory.ConcreteCategory.hom (c.ι.app j)) x；CategoryThe
ory.ConcreteCategory.hom (s.ι.app j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma CoconePt.fac_apply (s : Cocone F) (j : J) (x : F.obj j) :
    dsimp% CoconePt.desc hc s (c.ι.app j x) = s.ι.app j x :=
  ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x

/-- A colimit cocone for `F : J ⥤ PartOrdEmb` (with `J` filtered) can be
obtained from a colimit cocone for `F ⋙ forget _`. -/
/-
**PartOrdEmb.Limits.isColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb.Limits
`。
形式化陈述：isColimitCocone : IsColimit (cocone hc) where desc s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A colimit cocone for `F : J ⥤ PartOrdEmb` (with `J` filtered) can be
obtained from a colimit cocone for `F ⋙ forget _`.
-/
def isColimitCocone : IsColimit (cocone hc) where
  desc s := ofHom (CoconePt.desc hc s)
  fac s j := by
    ext x
    exact ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x
  uniq s m hm := by
    ext x
    obtain ⟨j, x, rfl⟩ := Types.jointly_surjective_of_isColimit hc x
    exact ((ConcreteCategory.congr_hom (hm j)) x).trans (CoconePt.fac_apply hc s j x).symm
/-
**PartOrdEmb.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasColimit F where
  exists_colimit := ⟨_, isColimitCocone (colimit.isColimit (F ⋙ forget _))⟩
/-
**PartOrdEmb.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesColimit F (forget _) :=
  preservesColimit_of_preserves_colimit_cocone
    (isColimitCocone (colimit.isColimit (F ⋙ forget _)))
    (colimit.isColimit (F ⋙ forget _))
/-
**PartOrdEmb.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasColimitsOfShape J PartOrdEmb.{u} where
/-
**PartOrdEmb.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesColimitsOfShape J (forget PartOrdEmb.{u}) where
/-
**PartOrdEmb.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ReflectsColimitsOfShape J (forget PartOrdEmb.{u}) :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms
/-
**PartOrdEmb.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasFilteredColimitsOfSize.{u, u} PartOrdEmb.{u} where
  HasColimitsOfShape _ := inferInstance
/-
**PartOrdEmb.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesFilteredColimitsOfSize.{u, u} (forget PartOrdEmb.{u}) where
  preserves_filtered_colimits _ := inferInstance

end Limits

variable {α : PartOrdEmb.{u}} (P : Set α → Prop)

/-- Given a predicate `P : Set α → Prop` on the underlying type of `α : PartOrdEmb.{u}`,
this is the functor `Subtype P ⥤ PartOrdEmb.{u}` which sends a subset `J` of `α`
satisfying `P` to the induced partially ordered type `J`. -/
@[simps obj map]
/-
**PartOrdEmb.functorOfPredicateSet** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb`。
形式化陈述：functorOfPredicateSet : Subtype P ⥤ PartOrdEmb.{u} where obj J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a predicate `P : Set α → Prop` on the underlying type of `α : PartOrdEmb.{
u}`,
this is the functor `Subtype P ⥤ PartOrdEmb.{u}` which sends a subset `J` of `α`
satisfying `P` to the induced partially ordered type `J`.
-/
def functorOfPredicateSet : Subtype P ⥤ PartOrdEmb.{u} where
  obj J := .of J.val
  map f :=
    ofHom {
      toFun x := ⟨x, leOfHom f x.prop⟩
      inj' _ _ _ := by aesop
      map_rel_iff' := by rfl }

/-- Given a predicate `P : Set α → Prop` on the underlying type of `α : PartOrdEmb.{u}`,
this is the cocone with point `α` given by all the inclusions of the subsets
satisfying `P`. -/
@[simps]
/-
**PartOrdEmb.coconeOfPredicateSet** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb`。
形式化陈述：coconeOfPredicateSet : Cocone (functorOfPredicateSet P) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a predicate `P : Set α → Prop` on the underlying type of `α : PartOrdEmb.{
u}`,
this is the cocone with point `α` given by all the inclusions of the subsets
satisfying `P`.
-/
def coconeOfPredicateSet : Cocone (functorOfPredicateSet P) where
  pt := α
  ι.app J := ofHom (OrderEmbedding.subtype _)

/-- Let `P` be a predicate on `Set α` where `α : PartOrdEmb`. We assume
that `Subtype P` is directed and nonempty, and that any `a : α` belongs
to some `J : Set α` satisfying `P`. Then, `α` is the colimit in the
category `PartOrdEmb` of these subsets. -/
/-
**PartOrdEmb.isColimitOfPredicateSet** 是 Mathlib 中的一个定义，位于命名空间 `PartOrdEmb`。
形式化陈述：isColimitOfPredicateSet [IsDirectedOrder (Subtype P)] [Nonempty (Subtype P
)] (hP : forall (a : α), exists (J : Set α), P J ∧ a in J) : IsColimit (coconeOf
PredicateSet P)
参数：Subtype P；Subtype P；hP : forall (a : α), exists (J : Set α), P J ∧ a in J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `P` be a predicate on `Set α` where `α : PartOrdEmb`. We assume
that `Subtype P` is directed and nonempty, and that any `a : α` belongs
to some `J : Set α` satisfying `P`. Then, `α` is the colimit in the
category `PartOrdEmb` of these subsets.
-/
noncomputable def isColimitOfPredicateSet
    [IsDirectedOrder (Subtype P)] [Nonempty (Subtype P)]
    (hP : ∀ (a : α), ∃ (J : Set α), P J ∧ a ∈ J) :
    IsColimit (coconeOfPredicateSet P) :=
  isColimitOfReflects (forget PartOrdEmb.{u}) (by
    refine Types.FilteredColimit.isColimitOf' _ _ (fun a ↦ ?_)
      (fun J x y h ↦ ⟨J, 𝟙 _, Subtype.ext h⟩)
    obtain ⟨J, hJ, ha⟩ := hP a
    exact ⟨⟨J, hJ⟩, ⟨a, ha⟩, rfl⟩)

end PartOrdEmb

