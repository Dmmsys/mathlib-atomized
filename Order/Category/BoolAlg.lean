/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.HeytAlg
public import Mathlib.Order.Hom.CompleteLattice

/-!
# The category of Boolean algebras

This defines `BoolAlg`, the category of Boolean algebras.
-/

@[expose] public section


open OrderDual Opposite Set

universe u

open CategoryTheory

/-- The category of Boolean algebras. -/
/-
**BoolAlg** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of Boolean algebras.
-/
structure BoolAlg where
  /-- Construct a bundled `BoolAlg` from the underlying type and typeclass. -/
  of ::
  /-- The underlying Boolean algebra. -/
  carrier : Type*
  [str : BooleanAlgebra carrier]

attribute [instance] BoolAlg.str

initialize_simps_projections BoolAlg (carrier → coe, -str)

namespace BoolAlg

/-
**BoolAlg.** 是 Mathlib 中的一个实例，位于命名空间 `BoolAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort BoolAlg (Type _) :=
  ⟨BoolAlg.carrier⟩

attribute [coe] BoolAlg.carrier

/-- The type of morphisms in `BoolAlg R`. -/
@[ext]
/-
**BoolAlg.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `BoolAlg`。
形式化陈述：BoolAlg → BoolAlg → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `BoolAlg R`.
-/
structure Hom (X Y : BoolAlg.{u}) where
  private mk ::
  /-- The underlying `BoundedLatticeHom`. -/
  hom' : BoundedLatticeHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**BoolAlg.** 是 Mathlib 中的一个实例，位于命名空间 `BoolAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category BoolAlg.{u} where
  Hom X Y := Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**BoolAlg.** 是 Mathlib 中的一个实例，位于命名空间 `BoolAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory BoolAlg (BoundedLatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `BoolAlg` back into a `BoundedLatticeHom`. -/
/-
**BoolAlg.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `BoolAlg.Hom`。
形式化陈述：{X Y : BoolAlg} → X.Hom Y → BoundedLatticeHom ↑X ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `BoolAlg` back into a `BoundedLatticeHom`.
-/
abbrev Hom.hom {X Y : BoolAlg.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BoolAlg) f

/-- Typecheck a `BoundedLatticeHom` as a morphism in `BoolAlg`. -/
/-
**BoolAlg.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `BoolAlg`。
形式化陈述：ofHom {X Y : Type u} [BooleanAlgebra X] [BooleanAlgebra Y] (f : BoundedLat
ticeHom X Y) : of X ⟶ of Y
参数：f : BoundedLatticeHom X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `BoundedLatticeHom` as a morphism in `BoolAlg`.
-/
abbrev ofHom {X Y : Type u} [BooleanAlgebra X] [BooleanAlgebra Y] (f : BoundedLatticeHom X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := BoolAlg) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**BoolAlg.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `BoolAlg.Hom.Simps`。
形式化陈述：(X Y : BoolAlg) → X.Hom Y → BoundedLatticeHom ↑X ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : BoolAlg.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**BoolAlg.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：coe_id {X : BoolAlg} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : BoolAlg} : (𝟙 X : X → X) = id := rfl

@[simp]
/-
**BoolAlg.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：coe_comp {X Y Z : BoolAlg} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g 
∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : BoolAlg} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
/-
**BoolAlg.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：forget_map {X Y : BoolAlg} (f : X ⟶ Y) : (forget BoolAlg).map f = (f : _ -
> _)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map {X Y : BoolAlg} (f : X ⟶ Y) :
    (forget BoolAlg).map f = (f : _ → _) := rfl

@[ext]
/-
**BoolAlg.ext** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：ext {X Y : BoolAlg} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : BoolAlg} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/-
**BoolAlg.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `BoolAlg`。
形式化陈述：coe_of (X : Type u) [BooleanAlgebra X] : (BoolAlg.of X : Type u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (X : Type u) [BooleanAlgebra X] : (BoolAlg.of X : Type u) = X := rfl

@[simp]
/-
**BoolAlg.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：hom_id {X : BoolAlg} : (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : BoolAlg} : (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _ := rfl

/- Provided for rewriting. -/
/-
**BoolAlg.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：id_apply (X : BoolAlg) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : BoolAlg；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (X : BoolAlg) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**BoolAlg.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：hom_comp {X Y Z : BoolAlg} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.hom.c
omp f.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : BoolAlg} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**BoolAlg.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：comp_apply {X Y Z : BoolAlg} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x =
 g (f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y Z : BoolAlg} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**BoolAlg.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：hom_ext {X Y : BoolAlg} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoolAlg.Hom.ext`：∀ {X Y : BoolAlg} {x y : X.Hom Y}, x.hom' = y.hom' → x 
= y
-/
lemma hom_ext {X Y : BoolAlg} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**BoolAlg.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：hom_ofHom {X Y : Type u} [BooleanAlgebra X] [BooleanAlgebra Y] (f : Bounde
dLatticeHom X Y) : (ofHom f).hom = f
参数：f : BoundedLatticeHom X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [BooleanAlgebra X] [BooleanAlgebra Y] (f : BoundedLatticeHom X Y) :
    (ofHom f).hom = f :=
  rfl

@[simp]
/-
**BoolAlg.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：ofHom_hom {X Y : BoolAlg} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : BoolAlg} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**BoolAlg.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：ofHom_id {X : Type u} [BooleanAlgebra X] : ofHom (BoundedLatticeHom.id _) 
= 𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [BooleanAlgebra X] : ofHom (BoundedLatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
/-
**BoolAlg.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：ofHom_comp {X Y Z : Type u} [BooleanAlgebra X] [BooleanAlgebra Y] [Boolean
Algebra Z] (f : BoundedLatticeHom X Y) (g : BoundedLatticeHom Y Z) : ofHom (g.co
mp f) = ofHom f ≫ ofHom g
参数：f : BoundedLatticeHom X Y；g : BoundedLatticeHom Y Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [BooleanAlgebra X] [BooleanAlgebra Y] [BooleanAlgebra Z]
    (f : BoundedLatticeHom X Y) (g : BoundedLatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**BoolAlg.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：ofHom_apply {X Y : Type u} [BooleanAlgebra X] [BooleanAlgebra Y] (f : Boun
dedLatticeHom X Y) (x : X) : (ofHom f) x = f x
参数：f : BoundedLatticeHom X Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [BooleanAlgebra X] [BooleanAlgebra Y]
    (f : BoundedLatticeHom X Y) (x : X) :
    (ofHom f) x = f x := rfl
/-
**BoolAlg.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：inv_hom_apply {X Y : BoolAlg} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x
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
lemma inv_hom_apply {X Y : BoolAlg} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp
/-
**BoolAlg.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `BoolAlg`。
形式化陈述：hom_inv_apply {X Y : BoolAlg} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s
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
lemma hom_inv_apply {X Y : BoolAlg} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp
/-
**BoolAlg.** 是 Mathlib 中的一个实例，位于命名空间 `BoolAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited BoolAlg :=
  ⟨of PUnit⟩

/-- Turn a `BoolAlg` into a `BddDistLat` by forgetting its complement operation. -/
/-
**BoolAlg.toBddDistLat** 是 Mathlib 中的一个定义，位于命名空间 `BoolAlg`。
形式化陈述：toBddDistLat (X : BoolAlg) : BddDistLat
参数：X : BoolAlg。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a `BoolAlg` into a `BddDistLat` by forgetting its complement operation.
-/
def toBddDistLat (X : BoolAlg) : BddDistLat :=
  .of X

@[simp]
/-
**BoolAlg.coe_toBddDistLat** 是 Mathlib 中的一个定理，位于命名空间 `BoolAlg`。
形式化陈述：coe_toBddDistLat (X : BoolAlg) : ↥X.toBddDistLat = ↥X
参数：X : BoolAlg。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toBddDistLat (X : BoolAlg) : ↥X.toBddDistLat = ↥X :=
  rfl
/-
**BoolAlg.hasForgetToBddDistLat** 是 Mathlib 中的一个实例，位于命名空间 `BoolAlg`。
形式化陈述：hasForgetToBddDistLat : HasForget₂ BoolAlg BddDistLat where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToBddDistLat : HasForget₂ BoolAlg BddDistLat where
  forget₂.obj X := .of X
  forget₂.map f := BddDistLat.ofHom f.hom

section

attribute [local instance] BoundedLatticeHomClass.toBiheytingHomClass

@[simps]
/-
**BoolAlg.hasForgetToHeytAlg** 是 Mathlib 中的一个实例，位于命名空间 `BoolAlg`。
形式化陈述：hasForgetToHeytAlg : HasForget₂ BoolAlg HeytAlg where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToHeytAlg : HasForget₂ BoolAlg HeytAlg where
  forget₂.obj X := .of X
  forget₂.map {X Y} f := HeytAlg.ofHom f.hom

end

/-- Constructs an equivalence between Boolean algebras from an order isomorphism between them. -/
@[simps]
/-
**BoolAlg.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `BoolAlg.Iso`。
形式化陈述：{α β : BoolAlg} → ↑α ≃o ↑β → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an equivalence between Boolean algebras from an order isomorphism bet
ween them.
-/
def Iso.mk {α β : BoolAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**BoolAlg.dual** 是 Mathlib 中的一个定义，位于命名空间 `BoolAlg`。
形式化陈述：dual : BoolAlg ⥤ BoolAlg where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : BoolAlg ⥤ BoolAlg where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `BoolAlg` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**BoolAlg.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `BoolAlg`。
形式化陈述：dualEquiv : BoolAlg ≌ BoolAlg where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `BoolAlg` and itself induced by `OrderDual` both ways.
-/
def dualEquiv : BoolAlg ≌ BoolAlg where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end BoolAlg

/-
**boolAlg_dual_comp_forget_to_bddDistLat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：boolAlg_dual_comp_forget_to_bddDistLat : BoolAlg.dual ⋙ forget₂ BoolAlg Bd
dDistLat = forget₂ BoolAlg BddDistLat ⋙ BddDistLat.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem boolAlg_dual_comp_forget_to_bddDistLat :
    BoolAlg.dual ⋙ forget₂ BoolAlg BddDistLat =
    forget₂ BoolAlg BddDistLat ⋙ BddDistLat.dual :=
  rfl

/-- The powerset functor. `Set` as a contravariant functor. -/
@[simps]
/-
**typeToBoolAlgOp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：typeToBoolAlgOp : Type u ⥤ BoolAlgᵒᵖ where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The powerset functor. `Set` as a contravariant functor.
-/
def typeToBoolAlgOp : Type u ⥤ BoolAlgᵒᵖ where
  obj X := op <| .of (Set X)
  map {X Y} f := Quiver.Hom.op (BoolAlg.ofHom (CompleteLatticeHom.setPreimage f))
