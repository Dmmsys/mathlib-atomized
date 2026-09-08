/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.BddDistLat
public import Mathlib.Order.Heyting.Hom

/-!
# The category of Heyting algebras

This file defines `HeytAlg`, the category of Heyting algebras.
-/

@[expose] public section


universe u

open CategoryTheory Opposite Order

/-- The category of Heyting algebras. -/
/-
**HeytAlg** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of Heyting algebras.
-/
structure HeytAlg where
  /-- The underlying Heyting algebra. -/
  carrier : Type*
  [str : HeytingAlgebra carrier]

attribute [instance] HeytAlg.str

initialize_simps_projections HeytAlg (carrier → coe, -str)

namespace HeytAlg

/-
**HeytAlg.** 是 Mathlib 中的一个实例，位于命名空间 `HeytAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort HeytAlg (Type _) :=
  ⟨HeytAlg.carrier⟩

attribute [coe] HeytAlg.carrier

/-- Construct a bundled `HeytAlg` from the underlying type and typeclass. -/
/-
**HeytAlg.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `HeytAlg`。
形式化陈述：of (X : Type*) [HeytingAlgebra X] : HeytAlg
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `HeytAlg` from the underlying type and typeclass.
-/
abbrev of (X : Type*) [HeytingAlgebra X] : HeytAlg := ⟨X⟩

/-- The type of morphisms in `HeytAlg R`. -/
@[ext]
/-
**HeytAlg.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `HeytAlg`。
形式化陈述：HeytAlg → HeytAlg → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `HeytAlg R`.
-/
structure Hom (X Y : HeytAlg.{u}) where
  private mk ::
  /-- The underlying `HeytingHom`. -/
  hom' : HeytingHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**HeytAlg.** 是 Mathlib 中的一个实例，位于命名空间 `HeytAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category HeytAlg.{u} where
  Hom X Y := Hom X Y
  id X := ⟨HeytingHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**HeytAlg.** 是 Mathlib 中的一个实例，位于命名空间 `HeytAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory HeytAlg (HeytingHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `HeytAlg` back into a `HeytingHom`. -/
/-
**HeytAlg.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `HeytAlg.Hom`。
形式化陈述：{X Y : HeytAlg} → X.Hom Y → HeytingHom ↑X ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `HeytAlg` back into a `HeytingHom`.
-/
abbrev Hom.hom {X Y : HeytAlg.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := HeytAlg) f

/-- Typecheck a `HeytingHom` as a morphism in `HeytAlg`. -/
/-
**HeytAlg.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `HeytAlg`。
形式化陈述：ofHom {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom
 X Y) : of X ⟶ of Y
参数：f : HeytingHom X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `HeytingHom` as a morphism in `HeytAlg`.
-/
abbrev ofHom {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := HeytAlg) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**HeytAlg.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `HeytAlg.Hom.Simps`。
形式化陈述：(X Y : HeytAlg) → X.Hom Y → HeytingHom ↑X ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : HeytAlg.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**HeytAlg.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：coe_id {X : HeytAlg} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : HeytAlg} : (𝟙 X : X → X) = id := rfl

@[simp]
/-
**HeytAlg.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：coe_comp {X Y Z : HeytAlg} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g 
∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : HeytAlg} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
/-
**HeytAlg.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：forget_map {X Y : HeytAlg} (f : X ⟶ Y) : (forget HeytAlg).map f = (f : _ -
> _)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map {X Y : HeytAlg} (f : X ⟶ Y) :
    (forget HeytAlg).map f = (f : _ → _) := rfl

@[ext]
/-
**HeytAlg.ext** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：ext {X Y : HeytAlg} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : HeytAlg} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/-
**HeytAlg.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `HeytAlg`。
形式化陈述：coe_of (X : Type u) [HeytingAlgebra X] : (HeytAlg.of X : Type u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (X : Type u) [HeytingAlgebra X] : (HeytAlg.of X : Type u) = X := rfl

@[simp]
/-
**HeytAlg.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：hom_id {X : HeytAlg} : (𝟙 X : X ⟶ X).hom = HeytingHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : HeytAlg} : (𝟙 X : X ⟶ X).hom = HeytingHom.id _ := rfl

/- Provided for rewriting. -/
/-
**HeytAlg.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：id_apply (X : HeytAlg) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : HeytAlg；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (X : HeytAlg) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**HeytAlg.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：hom_comp {X Y Z : HeytAlg} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.hom.c
omp f.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : HeytAlg} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**HeytAlg.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：comp_apply {X Y Z : HeytAlg} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x =
 g (f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y Z : HeytAlg} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**HeytAlg.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：hom_ext {X Y : HeytAlg} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HeytAlg.Hom.ext`：∀ {X Y : HeytAlg} {x y : X.Hom Y}, x.hom' = y.hom' → x 
= y
-/
lemma hom_ext {X Y : HeytAlg} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**HeytAlg.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：hom_ofHom {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] (f : Heytin
gHom X Y) : (ofHom f).hom = f
参数：f : HeytingHom X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) :
    (ofHom f).hom = f :=
  rfl

@[simp]
/-
**HeytAlg.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：ofHom_hom {X Y : HeytAlg} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : HeytAlg} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**HeytAlg.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：ofHom_id {X : Type u} [HeytingAlgebra X] : ofHom (HeytingHom.id _) = 𝟙 (of
 X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [HeytingAlgebra X] : ofHom (HeytingHom.id _) = 𝟙 (of X) := rfl

@[simp]
/-
**HeytAlg.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：ofHom_comp {X Y Z : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] [Heyting
Algebra Z] (f : HeytingHom X Y) (g : HeytingHom Y Z) : ofHom (g.comp f) = ofHom 
f ≫ ofHom g
参数：f : HeytingHom X Y；g : HeytingHom Y Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] [HeytingAlgebra Z]
    (f : HeytingHom X Y) (g : HeytingHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**HeytAlg.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：ofHom_apply {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] (f : Heyt
ingHom X Y) (x : X) : (ofHom f) x = f x
参数：f : HeytingHom X Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y]
    (f : HeytingHom X Y) (x : X) :
    (ofHom f) x = f x := rfl
/-
**HeytAlg.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：inv_hom_apply {X Y : HeytAlg} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x
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
lemma inv_hom_apply {X Y : HeytAlg} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp
/-
**HeytAlg.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `HeytAlg`。
形式化陈述：hom_inv_apply {X Y : HeytAlg} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s
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
lemma hom_inv_apply {X Y : HeytAlg} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp
/-
**HeytAlg.** 是 Mathlib 中的一个实例，位于命名空间 `HeytAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited HeytAlg :=
  ⟨of PUnit⟩

@[simps]
/-
**HeytAlg.hasForgetToLat** 是 Mathlib 中的一个实例，位于命名空间 `HeytAlg`。
形式化陈述：hasForgetToLat : HasForget₂ HeytAlg BddDistLat where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToLat : HasForget₂ HeytAlg BddDistLat where
  forget₂.obj X := .of X
  forget₂.map f := BddDistLat.ofHom f.hom

/-- Constructs an isomorphism of Heyting algebras from an order isomorphism between them. -/
@[simps]
/-
**HeytAlg.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `HeytAlg.Iso`。
形式化陈述：{α β : HeytAlg} → ↑α ≃o ↑β → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an isomorphism of Heyting algebras from an order isomorphism between 
them.
-/
def Iso.mk {α β : HeytAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

end HeytAlg

