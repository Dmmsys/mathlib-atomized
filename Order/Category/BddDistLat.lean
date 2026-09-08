/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.BddLat
public import Mathlib.Order.Category.DistLat

/-!
# The category of bounded distributive lattices

This defines `BddDistLat`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/

@[expose] public section


universe u

open CategoryTheory

/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
/-
**BddDistLat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of bounded distributive lattices with bounded lattice morphisms.
-/
structure BddDistLat extends DistLat where
  [isBoundedOrder : BoundedOrder toDistLat]

/-- The underlying distrib lattice of a bounded distributive lattice. -/
add_decl_doc BddDistLat.toDistLat

namespace BddDistLat

/-
**BddDistLat.** 是 Mathlib 中的一个实例，位于命名空间 `BddDistLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort BddDistLat Type* :=
  ⟨fun X => X.toDistLat⟩
/-
**BddDistLat.** 是 Mathlib 中的一个实例，位于命名空间 `BddDistLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : BddDistLat) : DistribLattice X :=
  X.toDistLat.str

attribute [instance] BddDistLat.isBoundedOrder

/-- Construct a bundled `BddDistLat` from a `BoundedOrder` `DistribLattice`. -/
/-
**BddDistLat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `BddDistLat`。
形式化陈述：of (α : Type*) [DistribLattice α] [BoundedOrder α] : BddDistLat where carr
ier
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `BddDistLat` from a `BoundedOrder` `DistribLattice`.
-/
abbrev of (α : Type*) [DistribLattice α] [BoundedOrder α] : BddDistLat where
  carrier := α
/-
**BddDistLat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `BddDistLat`。
形式化陈述：coe_of (α : Type*) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (α : Type*) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl

/-- The type of morphisms in `BddDistLat R`. -/
@[ext]
/-
**BddDistLat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `BddDistLat`。
形式化陈述：BddDistLat → BddDistLat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `BddDistLat R`.
-/
structure Hom (X Y : BddDistLat.{u}) where
  private mk ::
  /-- The underlying `BoundedLatticeHom`. -/
  hom' : BoundedLatticeHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**BddDistLat.** 是 Mathlib 中的一个实例，位于命名空间 `BddDistLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category BddDistLat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**BddDistLat.** 是 Mathlib 中的一个实例，位于命名空间 `BddDistLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory BddDistLat (BoundedLatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `BddDistLat` back into a `BoundedLatticeHom`. -/
/-
**BddDistLat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `BddDistLat.Hom`。
形式化陈述：{X Y : BddDistLat} → X.Hom Y → BoundedLatticeHom ↑X.toDistLat ↑Y.toDistLat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `BddDistLat` back into a `BoundedLatticeHom`.
-/
abbrev Hom.hom {X Y : BddDistLat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BddDistLat) f

/-- Typecheck a `BoundedLatticeHom` as a morphism in `BddDistLat`. -/
/-
**BddDistLat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `BddDistLat`。
形式化陈述：ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y
] [BoundedOrder Y] (f : BoundedLatticeHom X Y) : of X ⟶ of Y
参数：f : BoundedLatticeHom X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `BoundedLatticeHom` as a morphism in `BddDistLat`.
-/
abbrev ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y] [BoundedOrder Y]
    (f : BoundedLatticeHom X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := BddDistLat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**BddDistLat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `BddDistLat.Hom.Simps`。
形式化陈述：(X Y : BddDistLat) → X.Hom Y → BoundedLatticeHom ↑X.toDistLat ↑Y.toDistLat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : BddDistLat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**BddDistLat.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：coe_id {X : BddDistLat} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : BddDistLat} : (𝟙 X : X → X) = id := rfl

@[simp]
/-
**BddDistLat.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：coe_comp {X Y Z : BddDistLat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) =
 g ∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : BddDistLat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
/-
**BddDistLat.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：forget_map {X Y : BddDistLat} (f : X ⟶ Y) : (forget BddDistLat).map f = (f
 : _ -> _)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map {X Y : BddDistLat} (f : X ⟶ Y) :
    (forget BddDistLat).map f = (f : _ → _) := rfl

@[ext]
/-
**BddDistLat.ext** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：ext {X Y : BddDistLat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : BddDistLat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[simp]
/-
**BddDistLat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：hom_id {X : BddDistLat} : (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : BddDistLat} : (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _ := rfl

/- Provided for rewriting. -/
/-
**BddDistLat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：id_apply (X : BddDistLat) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : BddDistLat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (X : BddDistLat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**BddDistLat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：hom_comp {X Y Z : BddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.ho
m.comp f.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : BddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**BddDistLat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：comp_apply {X Y Z : BddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) 
x = g (f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y Z : BddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**BddDistLat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：hom_ext {X Y : BddDistLat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddDistLat.Hom.ext`：∀ {X Y : BddDistLat} {x y : X.Hom Y}, x.hom' = y.hom
' → x = y
-/
lemma hom_ext {X Y : BddDistLat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**BddDistLat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：hom_ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLatti
ce Y] [BoundedOrder Y] (f : BoundedLatticeHom X Y) : (ofHom f).hom = f
参数：f : BoundedLatticeHom X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
    [BoundedOrder Y] (f : BoundedLatticeHom X Y) :
    (ofHom f).hom = f :=
  rfl

@[simp]
/-
**BddDistLat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：ofHom_hom {X Y : BddDistLat} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : BddDistLat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**BddDistLat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：ofHom_id {X : Type u} [DistribLattice X] [BoundedOrder X] : ofHom (Bounded
LatticeHom.id _) = 𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [DistribLattice X] [BoundedOrder X] :
    ofHom (BoundedLatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
/-
**BddDistLat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：ofHom_comp {X Y Z : Type u} [DistribLattice X] [BoundedOrder X] [DistribLa
ttice Y] [BoundedOrder Y] [DistribLattice Z] [BoundedOrder Z] (f : BoundedLattic
eHom X Y) (g : BoundedLatticeHom Y Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : BoundedLatticeHom X Y；g : BoundedLatticeHom Y Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
    [BoundedOrder Y] [DistribLattice Z] [BoundedOrder Z]
    (f : BoundedLatticeHom X Y) (g : BoundedLatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**BddDistLat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：ofHom_apply {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLat
tice Y] [BoundedOrder Y] (f : BoundedLatticeHom X Y) (x : X) : (ofHom f) x = f x
参数：f : BoundedLatticeHom X Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
    [BoundedOrder Y]
    (f : BoundedLatticeHom X Y) (x : X) :
    (ofHom f) x = f x := rfl
/-
**BddDistLat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：inv_hom_apply {X Y : BddDistLat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x
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
lemma inv_hom_apply {X Y : BddDistLat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp
/-
**BddDistLat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `BddDistLat`。
形式化陈述：hom_inv_apply {X Y : BddDistLat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s
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
lemma hom_inv_apply {X Y : BddDistLat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp
/-
**BddDistLat.** 是 Mathlib 中的一个实例，位于命名空间 `BddDistLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited BddDistLat :=
  ⟨of PUnit⟩

/-- Turn a `BddDistLat` into a `BddLat` by forgetting it is distributive. -/
/-
**BddDistLat.toBddLat** 是 Mathlib 中的一个定义，位于命名空间 `BddDistLat`。
形式化陈述：toBddLat (X : BddDistLat) : BddLat
参数：X : BddDistLat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a `BddDistLat` into a `BddLat` by forgetting it is distributive.
-/
def toBddLat (X : BddDistLat) : BddLat :=
  .of X

@[simp]
/-
**BddDistLat.coe_toBddLat** 是 Mathlib 中的一个定理，位于命名空间 `BddDistLat`。
形式化陈述：coe_toBddLat (X : BddDistLat) : ↥X.toBddLat = ↥X
参数：X : BddDistLat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toBddLat (X : BddDistLat) : ↥X.toBddLat = ↥X :=
  rfl
/-
**BddDistLat.hasForgetToDistLat** 是 Mathlib 中的一个实例，位于命名空间 `BddDistLat`。
形式化陈述：hasForgetToDistLat : HasForget₂ BddDistLat DistLat where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToDistLat : HasForget₂ BddDistLat DistLat where
  forget₂.obj X := .of X
  forget₂.map f := DistLat.ofHom f.hom.toLatticeHom
/-
**BddDistLat.hasForgetToBddLat** 是 Mathlib 中的一个实例，位于命名空间 `BddDistLat`。
形式化陈述：hasForgetToBddLat : HasForget₂ BddDistLat BddLat where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToBddLat : HasForget₂ BddDistLat BddLat where
  forget₂.obj X := .of X
  forget₂.map f := BddLat.ofHom f.hom
/-
**BddDistLat.forget_bddLat_lat_eq_forget_distLat_lat** 是 Mathlib 中的一个定理，位于命名空间 `
BddDistLat`。
形式化陈述：forget_bddLat_lat_eq_forget_distLat_lat : forget₂ BddDistLat BddLat ⋙ forg
et₂ BddLat Lat = forget₂ BddDistLat DistLat ⋙ forget₂ DistLat Lat
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget_bddLat_lat_eq_forget_distLat_lat :
    forget₂ BddDistLat BddLat ⋙ forget₂ BddLat Lat =
      forget₂ BddDistLat DistLat ⋙ forget₂ DistLat Lat :=
  rfl

/-- Constructs an equivalence between bounded distributive lattices from an order isomorphism
between them. -/
@[simps]
/-
**BddDistLat.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `BddDistLat.Iso`。
形式化陈述：{α β : BddDistLat} → ↑α.toDistLat ≃o ↑β.toDistLat → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an equivalence between bounded distributive lattices from an order is
omorphism
between them.
-/
def Iso.mk {α β : BddDistLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := BddDistLat.ofHom e
  inv := BddDistLat.ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**BddDistLat.dual** 是 Mathlib 中的一个定义，位于命名空间 `BddDistLat`。
形式化陈述：dual : BddDistLat ⥤ BddDistLat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : BddDistLat ⥤ BddDistLat where
  obj X := of Xᵒᵈ
  map f := BddDistLat.ofHom f.hom.dual

/-- The equivalence between `BddDistLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**BddDistLat.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `BddDistLat`。
形式化陈述：dualEquiv : BddDistLat ≌ BddDistLat where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `BddDistLat` and itself induced by `OrderDual` both ways
.
-/
def dualEquiv : BddDistLat ≌ BddDistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end BddDistLat

/-
**bddDistLat_dual_comp_forget_to_distLat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddDistLat_dual_comp_forget_to_distLat : BddDistLat.dual ⋙ forget₂ BddDist
Lat DistLat = forget₂ BddDistLat DistLat ⋙ DistLat.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bddDistLat_dual_comp_forget_to_distLat :
    BddDistLat.dual ⋙ forget₂ BddDistLat DistLat =
      forget₂ BddDistLat DistLat ⋙ DistLat.dual :=
  rfl
