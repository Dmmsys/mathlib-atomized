/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Category.BddDistLat
public import Mathlib.Order.Category.FinPartOrd

/-!
# The category of finite bounded distributive lattices

This file defines `FinBddDistLat`, the category of finite distributive lattices with
bounded lattice homomorphisms.
-/

@[expose] public section


universe u

open CategoryTheory

/-- The category of finite distributive lattices with bounded lattice morphisms. -/
/-
**FinBddDistLat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finite distributive lattices with bounded lattice morphisms.
-/
structure FinBddDistLat extends BddDistLat where
  [isFintype : Fintype carrier]

namespace FinBddDistLat

/-
**FinBddDistLat.** 是 Mathlib 中的一个实例，位于命名空间 `FinBddDistLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort FinBddDistLat Type* :=
  ⟨fun X => X.carrier⟩
/-
**FinBddDistLat.** 是 Mathlib 中的一个实例，位于命名空间 `FinBddDistLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : FinBddDistLat) : DistribLattice X :=
  X.str
/-
**FinBddDistLat.** 是 Mathlib 中的一个实例，位于命名空间 `FinBddDistLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : FinBddDistLat) : BoundedOrder X :=
  X.isBoundedOrder

attribute [instance] FinBddDistLat.isFintype

/-- Construct a bundled `FinBddDistLat` from a `Fintype` `BoundedOrder` `DistribLattice`. -/
/-
**FinBddDistLat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `FinBddDistLat`。
形式化陈述：of (α : Type*) [DistribLattice α] [BoundedOrder α] [Fintype α] : FinBddDis
tLat where carrier
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `FinBddDistLat` from a `Fintype` `BoundedOrder` `DistribLatt
ice`.
-/
abbrev of (α : Type*) [DistribLattice α] [BoundedOrder α] [Fintype α] : FinBddDistLat where
  carrier := α

/-- Construct a bundled `FinBddDistLat` from a `Nonempty` `Fintype` `DistribLattice`. -/
/-
**FinBddDistLat.of'** 是 Mathlib 中的一个缩写定义，位于命名空间 `FinBddDistLat`。
形式化陈述：of' (α : Type*) [DistribLattice α] [Fintype α] [Nonempty α] : FinBddDistLa
t where carrier
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `FinBddDistLat` from a `Nonempty` `Fintype` `DistribLattice`
.
-/
abbrev of' (α : Type*) [DistribLattice α] [Fintype α] [Nonempty α] : FinBddDistLat where
  carrier := α
  isBoundedOrder := Fintype.toBoundedOrder α

/-- The type of morphisms in `FinBddDistLat R`. -/
@[ext]
/-
**FinBddDistLat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `FinBddDistLat`。
形式化陈述：FinBddDistLat → FinBddDistLat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `FinBddDistLat R`.
-/
structure Hom (X Y : FinBddDistLat.{u}) where
  private mk ::
  /-- The underlying `BoundedLatticeHom`. -/
  hom' : BoundedLatticeHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**FinBddDistLat.** 是 Mathlib 中的一个实例，位于命名空间 `FinBddDistLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category FinBddDistLat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**FinBddDistLat.** 是 Mathlib 中的一个实例，位于命名空间 `FinBddDistLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory FinBddDistLat (BoundedLatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `FinBddDistLat` back into a `BoundedLatticeHom`. -/
/-
**FinBddDistLat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `FinBddDistLat.Hom`。
形式化陈述：{X Y : FinBddDistLat} → X.Hom Y → BoundedLatticeHom ↑X.toDistLat ↑Y.toDist
Lat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `FinBddDistLat` back into a `BoundedLatticeHom`.
-/
abbrev Hom.hom {X Y : FinBddDistLat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := FinBddDistLat) f

/-- Typecheck a `BoundedLatticeHom` as a morphism in `FinBddDistLat`. -/
/-
**FinBddDistLat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `FinBddDistLat`。
形式化陈述：ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [Dist
ribLattice Y] [BoundedOrder Y] [Fintype Y] (f : BoundedLatticeHom X Y) : of X ⟶ 
of Y
参数：f : BoundedLatticeHom X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `BoundedLatticeHom` as a morphism in `FinBddDistLat`.
-/
abbrev ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
    [BoundedOrder Y] [Fintype Y]
    (f : BoundedLatticeHom X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := FinBddDistLat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**FinBddDistLat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `FinBddDistLat.Hom.Simps
`。
形式化陈述：(X Y : FinBddDistLat) → X.Hom Y → BoundedLatticeHom ↑X.toDistLat ↑Y.toDist
Lat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : FinBddDistLat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**FinBddDistLat.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：coe_id {X : FinBddDistLat} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : FinBddDistLat} : (𝟙 X : X → X) = id := rfl

@[simp]
/-
**FinBddDistLat.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：coe_comp {X Y Z : FinBddDistLat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z
) = g ∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : FinBddDistLat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
/-
**FinBddDistLat.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：forget_map {X Y : FinBddDistLat} (f : X ⟶ Y) : (forget FinBddDistLat).map 
f = (f : _ -> _)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map {X Y : FinBddDistLat} (f : X ⟶ Y) :
    (forget FinBddDistLat).map f = (f : _ → _) := rfl

@[ext]
/-
**FinBddDistLat.ext** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：ext {X Y : FinBddDistLat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f 
= g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : FinBddDistLat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[simp]
/-
**FinBddDistLat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：hom_id {X : FinBddDistLat} : (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : FinBddDistLat} : (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _ := rfl

/- Provided for rewriting. -/
/-
**FinBddDistLat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：id_apply (X : FinBddDistLat) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : FinBddDistLat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (X : FinBddDistLat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**FinBddDistLat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：hom_comp {X Y Z : FinBddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g
.hom.comp f.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : FinBddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**FinBddDistLat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：comp_apply {X Y Z : FinBddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ 
g) x = g (f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y Z : FinBddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**FinBddDistLat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：hom_ext {X Y : FinBddDistLat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FinBddDistLat.Hom.ext`：∀ {X Y : FinBddDistLat} {x y : X.Hom Y}, x.hom' =
 y.hom' → x = y
-/
lemma hom_ext {X Y : FinBddDistLat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**FinBddDistLat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：hom_ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [
DistribLattice Y] [BoundedOrder Y] [Fintype Y] (f : BoundedLatticeHom X Y) : (of
Hom f).hom = f
参数：f : BoundedLatticeHom X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
    [BoundedOrder Y] [Fintype Y] (f : BoundedLatticeHom X Y) : (ofHom f).hom = f := rfl

@[simp]
/-
**FinBddDistLat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：ofHom_hom {X Y : FinBddDistLat} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : FinBddDistLat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**FinBddDistLat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：ofHom_id {X : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] : of
Hom (BoundedLatticeHom.id _) = 𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] :
    ofHom (BoundedLatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
/-
**FinBddDistLat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：ofHom_comp {X Y Z : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X
] [DistribLattice Y] [BoundedOrder Y] [Fintype Y] [DistribLattice Z] [BoundedOrd
er Z] [Fintype Z] (f : BoundedLatticeHom X Y) (g : BoundedLatticeHom Y Z) : ofHo
m (g.comp f) = ofHom f ≫ ofHom g
参数：f : BoundedLatticeHom X Y；g : BoundedLatticeHom Y Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
    [BoundedOrder Y] [Fintype Y] [DistribLattice Z] [BoundedOrder Z] [Fintype Z]
    (f : BoundedLatticeHom X Y) (g : BoundedLatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**FinBddDistLat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：ofHom_apply {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X]
 [DistribLattice Y] [BoundedOrder Y] [Fintype Y] (f : BoundedLatticeHom X Y) (x 
: X) : (ofHom f) x = f x
参数：f : BoundedLatticeHom X Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
    [BoundedOrder Y] [Fintype Y]
    (f : BoundedLatticeHom X Y) (x : X) :
    (ofHom f) x = f x := rfl
/-
**FinBddDistLat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：inv_hom_apply {X Y : FinBddDistLat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) 
= x
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
lemma inv_hom_apply {X Y : FinBddDistLat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp
/-
**FinBddDistLat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `FinBddDistLat`。
形式化陈述：hom_inv_apply {X Y : FinBddDistLat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) 
= s
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
lemma hom_inv_apply {X Y : FinBddDistLat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp
/-
**FinBddDistLat.** 是 Mathlib 中的一个实例，位于命名空间 `FinBddDistLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited FinBddDistLat :=
  ⟨of PUnit⟩
/-
**FinBddDistLat.hasForgetToBddDistLat** 是 Mathlib 中的一个实例，位于命名空间 `FinBddDistLat`。
形式化陈述：hasForgetToBddDistLat : HasForget₂ FinBddDistLat BddDistLat where forget₂.
obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToBddDistLat : HasForget₂ FinBddDistLat BddDistLat where
  forget₂.obj X := .of X
  forget₂.map f := BddDistLat.ofHom f.hom
/-
**FinBddDistLat.hasForgetToFinPartOrd** 是 Mathlib 中的一个实例，位于命名空间 `FinBddDistLat`。
形式化陈述：hasForgetToFinPartOrd : HasForget₂ FinBddDistLat FinPartOrd where forget₂.
obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToFinPartOrd : HasForget₂ FinBddDistLat FinPartOrd where
  forget₂.obj X := .of X
  forget₂.map f := ConcreteCategory.ofHom (OrderHomClass.toOrderHom f.hom)

/-- Constructs an equivalence between finite distributive lattices from an order isomorphism
between them. -/
@[simps]
/-
**FinBddDistLat.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `FinBddDistLat.Iso`。
形式化陈述：{α β : FinBddDistLat} → ↑α.toDistLat ≃o ↑β.toDistLat → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an equivalence between finite distributive lattices from an order iso
morphism
between them.
-/
def Iso.mk {α β : FinBddDistLat.{u}} (e : α.carrier ≃o β.carrier) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**FinBddDistLat.dual** 是 Mathlib 中的一个定义，位于命名空间 `FinBddDistLat`。
形式化陈述：dual : FinBddDistLat ⥤ FinBddDistLat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : FinBddDistLat ⥤ FinBddDistLat where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `FinBddDistLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**FinBddDistLat.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FinBddDistLat`。
形式化陈述：dualEquiv : FinBddDistLat ≌ FinBddDistLat where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `FinBddDistLat` and itself induced by `OrderDual` both w
ays.
-/
def dualEquiv : FinBddDistLat ≌ FinBddDistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents (fun X => Iso.mk (α := X) <| OrderIso.dualDual X)
  counitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X)

end FinBddDistLat

/-
**finBddDistLat_dual_comp_forget_to_bddDistLat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finBddDistLat_dual_comp_forget_to_bddDistLat : FinBddDistLat.dual ⋙ forget
₂ FinBddDistLat BddDistLat = forget₂ FinBddDistLat BddDistLat ⋙ BddDistLat.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finBddDistLat_dual_comp_forget_to_bddDistLat :
    FinBddDistLat.dual ⋙ forget₂ FinBddDistLat BddDistLat =
      forget₂ FinBddDistLat BddDistLat ⋙ BddDistLat.dual :=
  rfl
