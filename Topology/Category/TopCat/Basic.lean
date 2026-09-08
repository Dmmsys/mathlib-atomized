/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Mario Carneiro
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Category instance for topological spaces

We introduce the bundled category `TopCat` of topological spaces together with the functors
`TopCat.discrete` and `TopCat.trivial` from the category of types to `TopCat` which equip a type
with the corresponding discrete, resp. trivial, topology. For a proof that these functors are left,
resp. right adjoint to the forgetful functor, see
`Mathlib/Topology/Category/TopCat/Adjunctions.lean`.
-/

@[expose] public section

assert_not_exists Module

open CategoryTheory TopologicalSpace Topology

universe u

/-- The category of topological spaces. -/
/-
**TopCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of topological spaces.
-/
structure TopCat where
  /-- The object in `TopCat` associated to a type equipped with the appropriate
  typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [str : TopologicalSpace carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `TopCat.of X` being printed as `{ carrier := X, str := ... }` by
`delabStructureInstance`. -/
@[app_delab TopCat.of]
meta def TopCat.delabOf : Delab := delabApp

end Notation

attribute [instance] TopCat.str

initialize_simps_projections TopCat (-str)

namespace TopCat

/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (TopCat) (Type u) :=
  ⟨TopCat.carrier⟩

attribute [coe] TopCat.carrier
/-
**TopCat.coe_of** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：coe_of (X : Type u) [TopologicalSpace X] : (of X : Type u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_of (X : Type u) [TopologicalSpace X] : (of X : Type u) = X :=
  rfl
/-
**TopCat.of_carrier** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：of_carrier (X : TopCat.{u}) : of X = X
参数：X : TopCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_carrier (X : TopCat.{u}) : of X = X := rfl

variable {X} in
/-- The type of morphisms in `TopCat`. -/
@[ext]
/-
**TopCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopCat`。
形式化陈述：TopCat → TopCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `TopCat`.
-/
structure Hom (X Y : TopCat.{u}) where
  private mk ::
  /-- The underlying `ContinuousMap`. -/
  hom' : C(X, Y)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category TopCat where
  Hom X Y := Hom X Y
  id X := ⟨ContinuousMap.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory.{u} TopCat (fun X Y => C(X, Y)) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `TopCat` back into a `ContinuousMap`. -/
/-
**TopCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Hom`。
形式化陈述：{X Y : TopCat} → X.Hom Y → C(↑X, ↑Y)
参数：↑X, ↑Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `TopCat` back into a `ContinuousMap`.
-/
abbrev Hom.hom {X Y : TopCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := TopCat) f

/-- Typecheck a `ContinuousMap` as a morphism in `TopCat`. -/
/-
**TopCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat`。
形式化陈述：ofHom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y
)) : of X ⟶ of Y
参数：f : C(X, Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `ContinuousMap` as a morphism in `TopCat`.
-/
abbrev ofHom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := TopCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**TopCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Hom.Simps`。
形式化陈述：(X Y : TopCat) → X.Hom Y → C(↑X, ↑Y)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : TopCat) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**TopCat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：hom_id {X : TopCat.{u}} : (𝟙 X : X ⟶ X).hom = ContinuousMap.id X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma hom_id {X : TopCat.{u}} : (𝟙 X : X ⟶ X).hom = ContinuousMap.id X := rfl

@[simp]
/-
**TopCat.id_app** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：id_app (X : TopCat.{u}) (x : ↑X) : (𝟙 X : X ⟶ X) x = x
参数：X : TopCat.{u}；x : ↑X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_app (X : TopCat.{u}) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl
/-
**TopCat.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：∀ (X : TopCat), ⇑(CategoryTheory.ConcreteCategory.hom (CategoryTheory.Cate
goryStruct.id X)) = id
参数：X : TopCat；CategoryTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct
.id X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_id (X : TopCat.{u}) : (𝟙 X : X → X) = id := rfl

@[simp]
/-
**TopCat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：hom_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.ho
m.comp f.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp]
/-
**TopCat.comp_app** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：comp_app {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X
 -> Z) x = g (f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_app {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) := rfl
/-
**TopCat.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(CategoryTheory.ConcreteCat
egory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(CategoryTheory.Concr
eteCategory.hom g) ∘ ⇑(CategoryTheory.ConcreteCategory.hom f)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.ConcreteCategory.hom (CategoryTheory.Categ
oryStruct.comp f g)；CategoryTheory.ConcreteCategory.hom g；CategoryTheory.Concret
eCategory.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X → Z) = g ∘ f := rfl

@[ext]
/-
**TopCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：hom_ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Hom.ext`：∀ {X Y : TopCat} {x y : X.Hom Y}, x.hom' = y.hom' → x = 
y
-/
lemma hom_ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[ext]
/-
**TopCat.ext** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[simp]
/-
**TopCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：hom_ofHom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(
X, Y)) : (ofHom f).hom = f
参数：f : C(X, Y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (ofHom f).hom = f := rfl

@[simp]
/-
**TopCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：ofHom_hom {X Y : TopCat.{u}} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : TopCat.{u}} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**TopCat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：ofHom_id {X : Type u} [TopologicalSpace X] : ofHom (ContinuousMap.id X) = 
𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [TopologicalSpace X] : ofHom (ContinuousMap.id X) = 𝟙 (of X) := rfl

@[simp]
/-
**TopCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：ofHom_comp {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [Top
ologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) : ofHom (g.comp f) = ofHom f ≫ ofHo
m g
参数：f : C(X, Y)；g : C(Y, Z)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**TopCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：ofHom_apply {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : 
C(X, Y)) (x : X) : (ofHom f) x = f x
参数：f : C(X, Y)；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    (ofHom f) x = f x := rfl
/-
**TopCat.hom_inv_id_apply** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：hom_inv_id_apply {X Y : TopCat.{u}} (f : X ≅ Y) (x : X) : f.inv (f.hom x) 
= x
参数：f : X ≅ Y；x : X。
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
lemma hom_inv_id_apply {X Y : TopCat.{u}} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x := by
  simp
/-
**TopCat.inv_hom_id_apply** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：inv_hom_id_apply {X Y : TopCat.{u}} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) 
= y
参数：f : X ≅ Y；y : Y。
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
lemma inv_hom_id_apply {X Y : TopCat.{u}} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y := by
  simp

/-- Morphisms in `TopCat` are equivalent to continuous maps. -/
@[simps]
/-
**TopCat.Hom.equivContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Hom`。
形式化陈述：(X Y : TopCat) → (X ⟶ Y) ≃ C(↑X, ↑Y)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms in `TopCat` are equivalent to continuous maps.
-/
def Hom.equivContinuousMap (X Y : TopCat.{u}) : (X ⟶ Y) ≃ C(X, Y) where
  toFun f := f.hom
  invFun f := ofHom f

/--
Replace a function coercion for a morphism `TopCat.of X ⟶ TopCat.of Y` with the definitionally
equal function coercion for a continuous map `C(X, Y)`.
-/
@[deprecated "No replacement" (since := "2026-04-23")]
/-
**TopCat.coe_of_of** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：coe_of_of {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : C(
X, Y)} {x} : @DFunLike.coe (TopCat.of X ⟶ TopCat.of Y) ((CategoryTheory.forget T
opCat).obj (TopCat.of X)) (fun _ => (CategoryTheory.forget TopCat).obj (TopCat.o
f Y)) ConcreteCategory.instFunLike (ofHom f) x = @DFunLike.coe C(X, Y) X (fun _ 
=> Y) _ f x
参数：X, Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace a function coercion for a morphism `TopCat.of X ⟶ TopCat.of Y` with the 
definitionally
equal function coercion for a continuous map `C(X, Y)`.
-/
theorem coe_of_of {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} {x} :
    @DFunLike.coe (TopCat.of X ⟶ TopCat.of Y) ((CategoryTheory.forget TopCat).obj (TopCat.of X))
      (fun _ ↦ (CategoryTheory.forget TopCat).obj (TopCat.of Y)) ConcreteCategory.instFunLike
      (ofHom f) x =
    @DFunLike.coe C(X, Y) X
      (fun _ ↦ Y) _
      f x :=
  rfl
/-
**TopCat.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
形式化陈述：inhabited : Inhabited TopCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited TopCat :=
  ⟨TopCat.of Empty⟩

/-- The discrete topology on any type. -/
/-
**TopCat.discrete** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：discrete : Type u ⥤ TopCat.{u} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete topology on any type.
-/
def discrete : Type u ⥤ TopCat.{u} where
  obj X := @of X ⊥
  map f := @ofHom _ _ ⊥ ⊥ <| @ContinuousMap.mk _ _ ⊥ ⊥ f continuous_bot
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Type u} : DiscreteTopology (discrete.obj X) :=
  ⟨rfl⟩

/-- The trivial topology on any type. -/
/-
**TopCat.trivial** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：trivial : Type u ⥤ TopCat.{u} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial topology on any type.
-/
def trivial : Type u ⥤ TopCat.{u} where
  obj X := @of X ⊤
  map f := @ofHom _ _ ⊤ ⊤ <| @ContinuousMap.mk _ _ ⊤ ⊤ f continuous_top

/-- Any homeomorphisms induces an isomorphism in `Top`. -/
@[simps]
/-
**TopCat.isoOfHomeo** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : X ≅ Y where hom
参数：f : X ≃ₜ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any homeomorphisms induces an isomorphism in `Top`.
-/
def isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ofHom f
  inv := ofHom f.symm

/-- Any isomorphism in `Top` induces a homeomorphism. -/
@[simps]
/-
**TopCat.homeoOfIso** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : X ≃ₜ Y where toFun
参数：f : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any isomorphism in `Top` induces a homeomorphism.
-/
def homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.hom.continuous
  continuous_invFun := f.inv.hom.continuous

@[simp]
/-
**TopCat.of_isoOfHomeo** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：of_isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : homeoOfIso (isoOfHomeo f) 
= f
参数：f : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.ext`：ext {h h' : X ≃ₜ Y} (H : forall x, h x = h' x) : h = h'
-/
theorem of_isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : homeoOfIso (isoOfHomeo f) = f := by
  ext
  rfl

@[simp]
/-
**TopCat.of_homeoOfIso** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：of_homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : isoOfHomeo (homeoOfIso f) =
 f
参数：f : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `TopCat.ext`：ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (w : forall x : X, f x 
= g x) : f = g
-/
theorem of_homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : isoOfHomeo (homeoOfIso f) = f := by
  ext
  rfl
/-
**TopCat.isIso_of_bijective_of_isOpenMap** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：isIso_of_bijective_of_isOpenMap {X Y : TopCat.{u}} (f : X ⟶ Y) (hfbij : Fu
nction.Bijective f) (hfcl : IsOpenMap f) : IsIso f
参数：f : X ⟶ Y；hfbij : Function.Bijective f；hfcl : IsOpenMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
-/
lemma isIso_of_bijective_of_isOpenMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hfbij : Function.Bijective f) (hfcl : IsOpenMap f) : IsIso f :=
  let e : X ≃ₜ Y :=
    (Equiv.ofBijective f hfbij).toHomeomorphOfContinuousOpen f.hom.continuous hfcl
  inferInstanceAs <| IsIso (TopCat.isoOfHomeo e).hom
/-
**TopCat.isIso_of_bijective_of_isClosedMap** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：isIso_of_bijective_of_isClosedMap {X Y : TopCat.{u}} (f : X ⟶ Y) (hfbij : 
Function.Bijective f) (hfcl : IsClosedMap f) : IsIso f
参数：f : X ⟶ Y；hfbij : Function.Bijective f；hfcl : IsClosedMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
-/
lemma isIso_of_bijective_of_isClosedMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hfbij : Function.Bijective f) (hfcl : IsClosedMap f) : IsIso f :=
  let e : X ≃ₜ Y :=
    (Equiv.ofBijective f hfbij).toHomeomorphOfContinuousClosed f.hom.continuous hfcl
  inferInstanceAs <| IsIso (TopCat.isoOfHomeo e).hom
/-
**TopCat.isIso_iff_isHomeomorph** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：isIso_iff_isHomeomorph {X Y : TopCat.{u}} (f : X ⟶ Y) : IsIso f ↔ IsHomeom
orph f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
· 使用引理 `TopCat.isIso_of_bijective_of_isOpenMap`：isIso_of_bijective_of_isOpenMap 
{X Y : TopCat.{u}} (f : X ⟶ Y) (hfbij : Function.Bijective f) (hfcl : IsOpenMap 
f) : IsIso f
· 使用定理 `IsHomeomorph.bijective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Functi
on.Bijective…
· 使用定理 `IsHomeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → IsOpen
Map f
-/
lemma isIso_iff_isHomeomorph {X Y : TopCat.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsHomeomorph f :=
  ⟨fun _ ↦ (homeoOfIso (asIso f)).isHomeomorph,
    fun H ↦ isIso_of_bijective_of_isOpenMap _ H.bijective H.isOpenMap⟩
/-
**TopCat.isOpenEmbedding_iff_comp_isIso** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：isOpenEmbedding_iff_comp_isIso {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z
) [IsIso g] : IsOpenEmbedding (f ≫ g) ↔ IsOpenEmbedding f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z
 : Type u_3} {g : Y → Z} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace 
Y]   [inst_2 : Topological…
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
-/
theorem isOpenEmbedding_iff_comp_isIso {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    IsOpenEmbedding (f ≫ g) ↔ IsOpenEmbedding f :=
  (TopCat.homeoOfIso (asIso g)).isOpenEmbedding.of_comp_iff f

@[simp]
/-
**TopCat.isOpenEmbedding_iff_comp_isIso'** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：isOpenEmbedding_iff_comp_isIso' {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ 
Z) [IsIso g] : IsOpenEmbedding (g ∘ f) ↔ IsOpenEmbedding f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.isOpenEmbedding_iff_comp_isIso`：isOpenEmbedding_iff_comp_isIso {X
 Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : IsOpenEmbedding (f ≫ g) ↔
 IsOpenEmbedding f
-/
theorem isOpenEmbedding_iff_comp_isIso' {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    IsOpenEmbedding (g ∘ f) ↔ IsOpenEmbedding f := by
  simp only
  exact isOpenEmbedding_iff_comp_isIso f g
/-
**TopCat.isOpenEmbedding_iff_isIso_comp** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：isOpenEmbedding_iff_isIso_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z
) [IsIso f] : IsOpenEmbedding (f ≫ g) ↔ IsOpenEmbedding g
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `Topology.IsOpenEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type
 u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologica
lSpace Y] [inst_2 :…
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
-/
theorem isOpenEmbedding_iff_isIso_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    IsOpenEmbedding (f ≫ g) ↔ IsOpenEmbedding g := by
  constructor
  · intro h
    convert! h.comp (TopCat.homeoOfIso (asIso f).symm).isOpenEmbedding
    exact congr_arg (DFunLike.coe ∘ ConcreteCategory.hom) (IsIso.inv_hom_id_assoc f g).symm
  · exact fun h => h.comp (TopCat.homeoOfIso (asIso f)).isOpenEmbedding

@[simp]
/-
**TopCat.isOpenEmbedding_iff_isIso_comp'** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：isOpenEmbedding_iff_isIso_comp' {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ 
Z) [IsIso f] : IsOpenEmbedding (g ∘ f) ↔ IsOpenEmbedding g
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.isOpenEmbedding_iff_isIso_comp`：isOpenEmbedding_iff_isIso_comp {X
 Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : IsOpenEmbedding (f ≫ g) ↔
 IsOpenEmbedding g
-/
theorem isOpenEmbedding_iff_isIso_comp' {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    IsOpenEmbedding (g ∘ f) ↔ IsOpenEmbedding g := by
  simp only
  exact isOpenEmbedding_iff_isIso_comp f g

/-- The `MorphismProperty` in `TopCat` of a morphism being an embedding. -/
/-
**TopCat.isEmbedding** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat`。
形式化陈述：isEmbedding : MorphismProperty TopCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `MorphismProperty` in `TopCat` of a morphism being an embedding.
-/
abbrev isEmbedding : MorphismProperty TopCat :=
  fun ⦃A X : TopCat⦄ (f : A ⟶ X) ↦ Topology.IsEmbedding f.hom

@[simp]
/-
**TopCat.isEmbedding_iff** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：isEmbedding_iff ⦃A X : TopCat⦄ (f : A ⟶ X) : isEmbedding f ↔ Topology.IsEm
bedding f.hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isEmbedding_iff ⦃A X : TopCat⦄ (f : A ⟶ X) : isEmbedding f ↔ Topology.IsEmbedding f.hom :=
  .rfl

/-- The constant morphism `X ⟶ Y` in `TopCat` given by `y : Y`. -/
/-
**TopCat.const** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：const {X Y : TopCat.{u}} (y : Y) : X ⟶ Y
参数：y : Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant morphism `X ⟶ Y` in `TopCat` given by `y : Y`.
-/
def const {X Y : TopCat.{u}} (y : Y) : X ⟶ Y :=
  ofHom ⟨fun _ ↦ y, by fun_prop⟩

@[simp]
/-
**TopCat.const_apply** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：const_apply {X Y : TopCat.{u}} (y : Y) (x : X) : const y x = y
参数：y : Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma const_apply {X Y : TopCat.{u}} (y : Y) (x : X) :
    const y x = y := rfl

end TopCat

