/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.PartOrd
public import Mathlib.Order.Hom.Lattice

/-!
# The category of lattices

This defines `Lat`, the category of lattices.

Note that `Lat` doesn't correspond to the literature definition of [`Lat`]
(https://ncatlab.org/nlab/show/Lat) as we don't require bottom or top elements. Instead, `Lat`
corresponds to `BddLat`.

## TODO

The free functor from `Lat` to `BddLat` is `X → WithTop (WithBot X)`.
-/

@[expose] public section

universe u

open CategoryTheory

/-- The category of lattices. -/
/-
**Lat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of lattices.
-/
structure Lat where
  /-- The underlying lattices. -/
  (carrier : Type*)
  [str : Lattice carrier]

attribute [instance] Lat.str

initialize_simps_projections Lat (carrier → coe, -str)

namespace Lat

/-
**Lat.** 是 Mathlib 中的一个实例，位于命名空间 `Lat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort Lat (Type _) :=
  ⟨Lat.carrier⟩

attribute [coe] Lat.carrier

/-- Construct a bundled `Lat` from the underlying type and typeclass. -/
/-
**Lat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `Lat`。
形式化陈述：of (X : Type*) [Lattice X] : Lat
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `Lat` from the underlying type and typeclass.
-/
abbrev of (X : Type*) [Lattice X] : Lat := ⟨X⟩

/-- The type of morphisms in `Lat R`. -/
@[ext]
/-
**Lat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Lat`。
形式化陈述：Lat → Lat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `Lat R`.
-/
structure Hom (X Y : Lat.{u}) where
  private mk ::
  /-- The underlying `LatticeHom`. -/
  hom' : LatticeHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Lat.** 是 Mathlib 中的一个实例，位于命名空间 `Lat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category Lat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨LatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Lat.** 是 Mathlib 中的一个实例，位于命名空间 `Lat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory Lat (LatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `Lat` back into a `LatticeHom`. -/
/-
**Lat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `Lat.Hom`。
形式化陈述：{X Y : Lat} → X.Hom Y → LatticeHom ↑X ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `Lat` back into a `LatticeHom`.
-/
abbrev Hom.hom {X Y : Lat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Lat) f

/-- Typecheck a `LatticeHom` as a morphism in `Lat`. -/
/-
**Lat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Lat`。
形式化陈述：ofHom {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) : of X ⟶
 of Y
参数：f : LatticeHom X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `LatticeHom` as a morphism in `Lat`.
-/
abbrev ofHom {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Lat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**Lat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `Lat.Hom.Simps`。
形式化陈述：(X Y : Lat) → X.Hom Y → LatticeHom ↑X ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : Lat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**Lat.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：coe_id {X : Lat} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : Lat} : (𝟙 X : X → X) = id := rfl

@[simp]
/-
**Lat.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：coe_comp {X Y Z : Lat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : Lat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
/-
**Lat.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：forget_map {X Y : Lat} (f : X ⟶ Y) : (forget Lat).map f = (f : _ -> _)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map {X Y : Lat} (f : X ⟶ Y) :
    (forget Lat).map f = (f : _ → _) := rfl

@[ext]
/-
**Lat.ext** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：ext {X Y : Lat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : Lat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/-
**Lat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `Lat`。
形式化陈述：coe_of (X : Type u) [Lattice X] : (Lat.of X : Type u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (X : Type u) [Lattice X] : (Lat.of X : Type u) = X := rfl

@[simp]
/-
**Lat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：hom_id {X : Lat} : (𝟙 X : X ⟶ X).hom = LatticeHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : Lat} : (𝟙 X : X ⟶ X).hom = LatticeHom.id _ := rfl

/- Provided for rewriting. -/
/-
**Lat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：id_apply (X : Lat) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : Lat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (X : Lat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**Lat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：hom_comp {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.hom.comp 
f.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**Lat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：comp_apply {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (
f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**Lat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：hom_ext {X Y : Lat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Lat.Hom.ext`：∀ {X Y : Lat} {x y : X.Hom Y}, x.hom' = y.hom' → x = y
-/
lemma hom_ext {X Y : Lat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**Lat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：hom_ofHom {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) : (o
fHom f).hom = f
参数：f : LatticeHom X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) : (ofHom f).hom = f :=
  rfl

@[simp]
/-
**Lat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：ofHom_hom {X Y : Lat} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : Lat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**Lat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：ofHom_id {X : Type u} [Lattice X] : ofHom (LatticeHom.id _) = 𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [Lattice X] : ofHom (LatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
/-
**Lat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：ofHom_comp {X Y Z : Type u} [Lattice X] [Lattice Y] [Lattice Z] (f : Latti
ceHom X Y) (g : LatticeHom Y Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : LatticeHom X Y；g : LatticeHom Y Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [Lattice X] [Lattice Y] [Lattice Z]
    (f : LatticeHom X Y) (g : LatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**Lat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：ofHom_apply {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) (x
 : X) : (ofHom f) x = f x
参数：f : LatticeHom X Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) (x : X) :
    (ofHom f) x = f x := rfl
/-
**Lat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：inv_hom_apply {X Y : Lat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x
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
lemma inv_hom_apply {X Y : Lat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp
/-
**Lat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Lat`。
形式化陈述：hom_inv_apply {X Y : Lat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s
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
lemma hom_inv_apply {X Y : Lat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp
/-
**Lat.hasForgetToPartOrd** 是 Mathlib 中的一个实例，位于命名空间 `Lat`。
形式化陈述：hasForgetToPartOrd : HasForget₂ Lat PartOrd where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToPartOrd : HasForget₂ Lat PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom f.hom

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
/-
**Lat.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `Lat.Iso`。
形式化陈述：{α β : Lat} → ↑α ≃o ↑β → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an isomorphism of lattices from an order isomorphism between them.
-/
def Iso.mk {α β : Lat.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**Lat.dual** 是 Mathlib 中的一个定义，位于命名空间 `Lat`。
形式化陈述：dual : Lat ⥤ Lat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : Lat ⥤ Lat where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `Lat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**Lat.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Lat`。
形式化陈述：dualEquiv : Lat ≌ Lat where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `Lat` and itself induced by `OrderDual` both ways.
-/
def dualEquiv : Lat ≌ Lat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end Lat

/-
**Lat_dual_comp_forget_to_partOrd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Lat_dual_comp_forget_to_partOrd : Lat.dual ⋙ forget₂ Lat PartOrd = forget₂
 Lat PartOrd ⋙ PartOrd.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Lat_dual_comp_forget_to_partOrd :
    Lat.dual ⋙ forget₂ Lat PartOrd = forget₂ Lat PartOrd ⋙ PartOrd.dual :=
  rfl
