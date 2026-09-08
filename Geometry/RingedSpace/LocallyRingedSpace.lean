/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Geometry.RingedSpace.Stalks

/-!
# The category of locally ringed spaces

We define (bundled) locally ringed spaces (as `SheafedSpace CommRing` along with the fact that the
stalks are local rings), and morphisms between these (morphisms in `SheafedSpace` with
`IsLocalHom` on the stalk maps).
-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe u

open CategoryTheory

open TopCat

open TopologicalSpace Topology

open Opposite

open CategoryTheory.Category CategoryTheory.Functor

namespace AlgebraicGeometry

/-- A `LocallyRingedSpace` is a topological space equipped with a sheaf of commutative rings
such that all the stalks are local rings.

A morphism of locally ringed spaces is a morphism of ringed spaces
such that the morphisms induced on stalks are local ring homomorphisms. -/
/-
**AlgebraicGeometry.LocallyRingedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `LocallyRingedSpace` is a topological space equipped with a sheaf of commutati
ve rings
such that all the stalks are local rings.

A morphism of locally ringed spaces is a morphism of ringed spaces
such that the morphisms induced on stalks are local ring homomorphisms.
-/
structure LocallyRingedSpace extends SheafedSpace CommRingCat.{u} where
  /-- Stalks of a locally ringed space are local rings. -/
  isLocalRing : ∀ x, IsLocalRing (presheaf.stalk x)

attribute [instance] LocallyRingedSpace.isLocalRing

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- An alias for `toSheafedSpace`, where the result type is a `RingedSpace`.
This allows us to use dot-notation for the `RingedSpace` namespace.
-/
/-
**AlgebraicGeometry.LocallyRingedSpace.toRingedSpace** 是 Mathlib 中的一个缩写定义，位于命名空间
 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：toRingedSpace : RingedSpace
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alias for `toSheafedSpace`, where the result type is a `RingedSpace`.
This allows us to use dot-notation for the `RingedSpace` namespace.
-/
abbrev toRingedSpace : RingedSpace :=
  X.toSheafedSpace

/-- The underlying topological space of a locally ringed space. -/
@[implicit_reducible]
/-
**AlgebraicGeometry.LocallyRingedSpace.toTopCat** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.LocallyRingedSpace`。
形式化陈述：toTopCat : TopCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying topological space of a locally ringed space.
-/
def toTopCat : TopCat :=
  X.1.carrier
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort LocallyRingedSpace (Type u) :=
  ⟨fun X : LocallyRingedSpace => (X.toTopCat : Type _)⟩
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X) : IsLocalRing (X.presheaf.stalk x) :=
  X.isLocalRing x

-- PROJECT: how about a typeclass "HasStructureSheaf" to mediate the 𝒪 notation, rather
-- than defining it over and over for `PresheafedSpace`, `LocallyRingedSpace`, `Scheme`, etc.
/-- The structure sheaf of a locally ringed space. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure sheaf of a locally ringed space.
-/
def 𝒪 : Sheaf CommRingCat X.toTopCat :=
  X.sheaf

/-- A morphism of locally ringed spaces is a morphism of ringed spaces
such that the morphisms induced on stalks are local ring homomorphisms. -/
@[ext]
/-
**AlgebraicGeometry.LocallyRingedSpace.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebrai
cGeometry.LocallyRingedSpace`。
形式化陈述：AlgebraicGeometry.LocallyRingedSpace → AlgebraicGeometry.LocallyRingedSpac
e → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of locally ringed spaces is a morphism of ringed spaces
such that the morphisms induced on stalks are local ring homomorphisms.
-/
structure Hom (X Y : LocallyRingedSpace.{u}) : Type _
    extends X.toPresheafedSpace.Hom Y.toPresheafedSpace where
  /-- the underlying morphism induces a local ring homomorphism on stalks -/
  prop : ∀ x, IsLocalHom (toHom.stalkMap x).hom

/-- A morphism of locally ringed spaces as a morphism of sheafed spaces. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.Hom.toShHom** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.LocallyRingedSpace.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.LocallyRingedSpace} → X.Hom Y → (X.toSheafedSpace
 ⟶ Y.toSheafedSpace)
参数：X.toSheafedSpace ⟶ Y.toSheafedSpace。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of locally ringed spaces as a morphism of sheafed spaces.
-/
abbrev Hom.toShHom {X Y : LocallyRingedSpace.{u}} (f : X.Hom Y) :
  X.toSheafedSpace ⟶ Y.toSheafedSpace := InducedCategory.homMk f.1

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.Hom.toShHom_mk** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.LocallyRingedSpace.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.LocallyRingedSpace} (f : X.Hom Y.toPresheafedSp
ace)   (hf : ∀ (x : ↑↑X.toPresheafedSpace), IsLocalHom (CommRingCat.Hom.hom (f.s
talkMap x))),   { toHom := f, prop := hf }.toShHom = CategoryTheory.InducedCateg
ory.homMk f
参数：f : X.Hom Y.toPresheafedSpace；hf : ∀ (x : ↑↑X.toPresheafedSpace), IsLocalHom 
(CommRingCat.Hom.hom (f.stalkMap x))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.toShHom_mk {X Y : LocallyRingedSpace.{u}}
    (f : X.toPresheafedSpace.Hom Y.toPresheafedSpace) (hf) :
  Hom.toShHom ⟨f, hf⟩ = InducedCategory.homMk f := rfl
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Quiver LocallyRingedSpace :=
  ⟨Hom⟩
/-
**AlgebraicGeometry.LocallyRingedSpace.Hom.ext'** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.LocallyRingedSpace.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.LocallyRingedSpace} {f g : X ⟶ Y}, f.toHom = g.
toHom → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[ext] lemma Hom.ext' {X Y : LocallyRingedSpace.{u}} {f g : X ⟶ Y}
    (h : f.toHom = g.toHom) :
    f = g := by cases f; cases g; congr

/-- A morphism of locally ringed spaces `f : X ⟶ Y` induces
a local ring homomorphism from `Y.stalk (f x)` to `X.stalk x` for any `x : X`.
-/
/-
**AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.LocallyRingedSpace.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.LocallyRingedSpace} →   (f : X ⟶ Y) →     (x : ↑X
.toTopCat) → Y.presheaf.stalk ((CategoryTheory.ConcreteCategory.hom f.base) x) ⟶
 X.presheaf.stalk x
参数：f : X ⟶ Y；x : ↑X.toTopCat；(CategoryTheory.ConcreteCategory.hom f.base) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of locally ringed spaces `f : X ⟶ Y` induces
a local ring homomorphism from `Y.stalk (f x)` to `X.stalk x` for any `x : X`.
-/
noncomputable def Hom.stalkMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    Y.presheaf.stalk (f.1.1 x) ⟶ X.presheaf.stalk x :=
  f.toShHom.hom.stalkMap x

@[instance]
/-
**AlgebraicGeometry.LocallyRingedSpace.isLocalHomStalkMap** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：isLocalHomStalkMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) : Is
LocalHom (f.stalkMap x).hom
参数：f : X ⟶ Y；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.Hom.prop`：∀ {X Y : AlgebraicGeometr
y.LocallyRingedSpace} (self : X.Hom Y) (x : ↑↑X.toPresheafedSpace),   IsLocalHom
 (CommRingCat.Hom.hom (self.stalkMa…
-/
theorem isLocalHomStalkMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    IsLocalHom (f.stalkMap x).hom :=
  f.2 x
/-
**AlgebraicGeometry.LocallyRingedSpace.isLocalHomStalkMap'** 是 Mathlib 中的一个实例，位于
命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：isLocalHomStalkMap' {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) : I
sLocalHom (f.toHom.stalkMap x).hom
参数：f : X ⟶ Y；x : X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.isLocalHomStalkMap`：isLocalHomStalk
Map {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) : IsLocalHom (f.stalkMap 
x).hom
-/
instance isLocalHomStalkMap' {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    IsLocalHom (f.toHom.stalkMap x).hom :=
  isLocalHomStalkMap f x

@[instance]
/-
**AlgebraicGeometry.LocallyRingedSpace.isLocalHomValStalkMap** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：isLocalHomValStalkMap {X Y : LocallyRingedSpace.{u}} (f : Hom X Y) (x : X)
 : IsLocalHom (f.stalkMap x).hom
参数：f : Hom X Y；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.Hom.prop`：∀ {X Y : AlgebraicGeometr
y.LocallyRingedSpace} (self : X.Hom Y) (x : ↑↑X.toPresheafedSpace),   IsLocalHom
 (CommRingCat.Hom.hom (self.stalkMa…
-/
theorem isLocalHomValStalkMap {X Y : LocallyRingedSpace.{u}} (f : Hom X Y) (x : X) :
    IsLocalHom (f.stalkMap x).hom :=
  f.2 x

set_option backward.isDefEq.respectTransparency false in
/-- The identity morphism on a locally ringed space. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.id** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
形式化陈述：id (X : LocallyRingedSpace.{u}) : Hom X X
参数：X : LocallyRingedSpace.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism on a locally ringed space.
-/
def id (X : LocallyRingedSpace.{u}) : Hom X X :=
  ⟨𝟙 X.toPresheafedSpace, fun x => by dsimp; rw [PresheafedSpace.stalkMap.id]; infer_instance⟩
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : LocallyRingedSpace.{u}) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of locally ringed spaces. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.comp** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.LocallyRingedSpace`。
形式化陈述：comp {X Y Z : LocallyRingedSpace.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X 
Z where toHom
参数：f : Hom X Y；g : Hom Y Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms of locally ringed spaces.
-/
def comp {X Y Z : LocallyRingedSpace.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toHom := (f.toHom ≫ g.toHom : X.toPresheafedSpace ⟶ Z.toPresheafedSpace)
  prop x := by
    rw [PresheafedSpace.stalkMap.comp]
    apply +allowSynthFailures RingHom.isLocalHom_comp
    all_goals apply isLocalHomValStalkMap

/-- The category of locally ringed spaces. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of locally ringed spaces.
-/
instance : Category LocallyRingedSpace.{u} where
  Hom := Hom
  id := id
  comp f g := comp f g

/-- The forgetful functor from `LocallyRingedSpace` to `SheafedSpace CommRing`. -/
@[simps]
/-
**AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace** 是 Mathlib 中的一个定义，位
于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：forgetToSheafedSpace : LocallyRingedSpace.{u} ⥤ SheafedSpace CommRingCat.{
u} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `LocallyRingedSpace` to `SheafedSpace CommRing`.
-/
def forgetToSheafedSpace : LocallyRingedSpace.{u} ⥤ SheafedSpace CommRingCat.{u} where
  obj X := X.toSheafedSpace
  map f := InducedCategory.homMk f.1

/-- The canonical map `X ⟶ Spec Γ(X, ⊤)`. This is the unit of the `Γ-Spec` adjunction. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `X ⟶ Spec Γ(X, ⊤)`. This is the unit of the `Γ-Spec` adjunctio
n.
-/
instance : forgetToSheafedSpace.Faithful where
  map_injective h := by
    ext : 1
    exact congr_arg InducedCategory.Hom.hom h

/-- Constructor for morphisms in `LocallyRingedSpace`. -/
@[simps toHom]
/-
**AlgebraicGeometry.LocallyRingedSpace.homMk** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.LocallyRingedSpace`。
形式化陈述：homMk {X Y : LocallyRingedSpace.{u}} (f : X.toSheafedSpace ⟶ Y.toSheafedSp
ace) (h : forall (x : X), IsLocalHom (f.hom.stalkMap x).hom
参数：f : X.toSheafedSpace ⟶ Y.toSheafedSpace。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `LocallyRingedSpace`.
-/
def homMk {X Y : LocallyRingedSpace.{u}} (f : X.toSheafedSpace ⟶ Y.toSheafedSpace)
    (h : ∀ (x : X), IsLocalHom (f.hom.stalkMap x).hom := by infer_instance) : X ⟶ Y where
  toHom := f.hom
  prop := by assumption

/-- The forgetful functor from `LocallyRingedSpace` to `Top`. -/
@[simps!]
/-
**AlgebraicGeometry.LocallyRingedSpace.forgetToTop** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.LocallyRingedSpace`。
形式化陈述：forgetToTop : LocallyRingedSpace.{u} ⥤ TopCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `LocallyRingedSpace` to `Top`.
-/
def forgetToTop : LocallyRingedSpace.{u} ⥤ TopCat.{u} :=
  forgetToSheafedSpace ⋙ SheafedSpace.forget _

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.id_toHom** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.LocallyRingedSpace`。
形式化陈述：id_toHom (X : LocallyRingedSpace.{u}) : Hom.toHom (𝟙 X) = 𝟙 X.toPresheafed
Space
参数：X : LocallyRingedSpace.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_toHom (X : LocallyRingedSpace.{u}) :
    Hom.toHom (𝟙 X) = 𝟙 X.toPresheafedSpace :=
  rfl

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.comp_toHom** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.LocallyRingedSpace`。
形式化陈述：comp_toHom {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫
 g).toHom = (f.toHom ≫ g.toHom : X.toPresheafedSpace ⟶ Z.toPresheafedSpace)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_toHom {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toHom = (f.toHom ≫ g.toHom : X.toPresheafedSpace ⟶ Z.toPresheafedSpace) :=
  rfl

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.comp_toShHom** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.LocallyRingedSpace`。
形式化陈述：comp_toShHom {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f
 ≫ g).toShHom = f.toShHom ≫ g.toShHom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_toShHom {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toShHom = f.toShHom ≫ g.toShHom :=
  rfl

/-- A variant of `id_toShHom'` that works with `𝟙 X` instead of `id X`. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.id_toShHom'** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.LocallyRingedSpace`。
形式化陈述：∀ (X : AlgebraicGeometry.LocallyRingedSpace),   AlgebraicGeometry.LocallyR
ingedSpace.Hom.toShHom (CategoryTheory.CategoryStruct.id X) =     CategoryTheory
.CategoryStruct.id X.toSheafedSpace
参数：X : AlgebraicGeometry.LocallyRingedSpace；CategoryTheory.CategoryStruct.id X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `id_toShHom'` that works with `𝟙 X` instead of `id X`.
-/
@[simp] theorem id_toShHom' (X : LocallyRingedSpace.{u}) :
    Hom.toShHom (𝟙 X) = 𝟙 X.toSheafedSpace :=
  rfl
/-
**AlgebraicGeometry.LocallyRingedSpace.comp_base** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.LocallyRingedSpace`。
形式化陈述：comp_base {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ 
g).base = f.base ≫ g.base
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_base {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl
/-
**AlgebraicGeometry.LocallyRingedSpace.comp_c** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.LocallyRingedSpace`。
形式化陈述：comp_c {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).
c = g.c ≫ (Presheaf.pushforward _ g.base).map f.c
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_c {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).c = g.c ≫ (Presheaf.pushforward _ g.base).map f.c :=
  rfl
/-
**AlgebraicGeometry.LocallyRingedSpace.comp_c_app** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.LocallyRingedSpace`。
形式化陈述：comp_c_app {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : (
Opens Z)ᵒᵖ) : (f ≫ g).c.app U = g.c.app U ≫ f.c.app (op <| (Opens.map g.base).ob
j U.unop)
参数：f : X ⟶ Y；g : Y ⟶ Z；U : (Opens Z)ᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_c_app {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : (Opens Z)ᵒᵖ) :
    (f ≫ g).c.app U = g.c.app U ≫ f.c.app (op <| (Opens.map g.base).obj U.unop) :=
  rfl

/-- Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` as _sheafed_
spaces can be lifted to a morphism `X ⟶ Y` as locally ringed spaces.

See also `isoOfSheafedSpaceIso`.
-/
@[simps! toHom]
/-
**AlgebraicGeometry.LocallyRingedSpace.homOfSheafedSpaceHomOfIsIso** 是 Mathlib 中
的一个定义，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：homOfSheafedSpaceHomOfIsIso {X Y : LocallyRingedSpace.{u}} (f : X.toSheafe
dSpace ⟶ Y.toSheafedSpace) [IsIso f] : X ⟶ Y where toHom
参数：f : X.toSheafedSpace ⟶ Y.toSheafedSpace。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` 
as _sheafed_
spaces can be lifted to a morphism `X ⟶ Y` as locally ringed spaces.

See also `isoOfSheafedSpaceIso`.
-/
def homOfSheafedSpaceHomOfIsIso {X Y : LocallyRingedSpace.{u}}
    (f : X.toSheafedSpace ⟶ Y.toSheafedSpace) [IsIso f] : X ⟶ Y where
  toHom := f.hom
  prop _ :=
    -- Here we need to see that the stalk maps are really local ring homomorphisms.
    -- This can be solved by type class inference, because stalk maps of isomorphisms
    -- are isomorphisms and isomorphisms are local ring homomorphisms.
    inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` as _sheafed_
spaces can be lifted to an isomorphism `X ⟶ Y` as locally ringed spaces.

This is related to the property that the functor `forgetToSheafedSpace` reflects isomorphisms.
In fact, it is slightly stronger as we do not require `f` to come from a morphism between
_locally_ ringed spaces.
-/
/-
**AlgebraicGeometry.LocallyRingedSpace.isoOfSheafedSpaceIso** 是 Mathlib 中的一个定义，位
于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：isoOfSheafedSpaceIso {X Y : LocallyRingedSpace.{u}} (f : X.toSheafedSpace 
≅ Y.toSheafedSpace) : X ≅ Y where hom
参数：f : X.toSheafedSpace ≅ Y.toSheafedSpace。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` 
as _sheafed_
spaces can be lifted to an isomorphism `X ⟶ Y` as locally ringed spaces.

This is related to the property that the functor `forgetToSheafedSpace` reflects
 isomorphisms.
In fact, it is slightly stronger as we do not require `f` to come from a morphis
m between
_locally_ ringed spaces.
-/
def isoOfSheafedSpaceIso {X Y : LocallyRingedSpace.{u}} (f : X.toSheafedSpace ≅ Y.toSheafedSpace) :
    X ≅ Y where
  hom := homOfSheafedSpaceHomOfIsIso f.hom
  inv := homOfSheafedSpaceHomOfIsIso f.inv
  hom_inv_id := by
    ext : 1
    dsimp
    rw [← InducedCategory.comp_hom, f.hom_inv_id, SheafedSpace.id_hom]
  inv_hom_id := by
    ext : 1
    dsimp
    rw [← InducedCategory.comp_hom, f.inv_hom_id, SheafedSpace.id_hom]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : forgetToSheafedSpace.ReflectsIsomorphisms where
  reflects f _ := (isoOfSheafedSpaceIso (asIso (forgetToSheafedSpace.map f))).isIso_hom
/-
**AlgebraicGeometry.LocallyRingedSpace.is_sheafedSpace_iso** 是 Mathlib 中的一个实例，位于
命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：is_sheafedSpace_iso {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsIso f] :
 IsIso f.toShHom
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance is_sheafedSpace_iso {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsIso f] :
    IsIso f.toShHom :=
  LocallyRingedSpace.forgetToSheafedSpace.map_isIso f

/-- The restriction of a locally ringed space along an open embedding.
-/
@[simps!]
/-
**AlgebraicGeometry.LocallyRingedSpace.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.LocallyRingedSpace`。
形式化陈述：restrict {U : TopCat.{u}} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopCat
} (h : IsOpenEmbedding f) : LocallyRingedSpace where isLocalRing
参数：X : LocallyRingedSpace.{u}；h : IsOpenEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a locally ringed space along an open embedding.
-/
def restrict {U : TopCat.{u}} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopCat}
    (h : IsOpenEmbedding f) : LocallyRingedSpace where
  isLocalRing := by
    intro x
    -- We show that the stalk of the restriction is isomorphic to the original stalk,
    apply @RingEquiv.isLocalRing _ _ _ (X.isLocalRing (f x))
    exact (X.restrictStalkIso h x).symm.commRingCatIsoToRingEquiv
  toSheafedSpace := X.toSheafedSpace.restrict h

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from the restriction to the subspace. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.ofRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.LocallyRingedSpace`。
形式化陈述：ofRestrict {U : TopCat.{u}} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopC
at} (h : IsOpenEmbedding f) : X.restrict h ⟶ X
参数：X : LocallyRingedSpace.{u}；h : IsOpenEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the restriction to the subspace.
-/
def ofRestrict {U : TopCat.{u}} (X : LocallyRingedSpace.{u})
    {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f) : X.restrict h ⟶ X :=
  ⟨X.toPresheafedSpace.ofRestrict h, fun _ => inferInstance⟩

/-- The restriction of a locally ringed space `X` to the top subspace is isomorphic to `X` itself.
-/
/-
**AlgebraicGeometry.LocallyRingedSpace.restrictTopIso** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：restrictTopIso (X : LocallyRingedSpace.{u}) : X.restrict (Opens.isOpenEmbe
dding ⊤) ≅ X
参数：X : LocallyRingedSpace.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a locally ringed space `X` to the top subspace is isomorphic 
to `X` itself.
-/
def restrictTopIso (X : LocallyRingedSpace.{u}) :
    X.restrict (Opens.isOpenEmbedding ⊤) ≅ X :=
  isoOfSheafedSpaceIso X.toSheafedSpace.restrictTopIso

/-- The global sections, notated Gamma.
-/
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The global sections, notated Gamma.
-/
def Γ : LocallyRingedSpace.{u}ᵒᵖ ⥤ CommRingCat.{u} :=
  forgetToSheafedSpace.op ⋙ SheafedSpace.Γ
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_def : Γ = forgetToSheafedSpace.op ⋙ SheafedSpace.Γ :=
  rfl

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_obj (X : LocallyRingedSpace.{u}ᵒᵖ) : Γ.obj X = X.unop.presheaf.obj (op ⊤) :=
  rfl
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_obj_op (X : LocallyRingedSpace.{u}) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_map {X Y : LocallyRingedSpace.{u}ᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.c.app (op ⊤) :=
  rfl
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_map_op {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl

/-- The empty locally ringed space. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.empty** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.LocallyRingedSpace`。
形式化陈述：empty : LocallyRingedSpace.{u} where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty locally ringed space.
-/
def empty : LocallyRingedSpace.{u} where
  carrier := TopCat.of PEmpty
  presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  isLocalRing x := PEmpty.elim x
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EmptyCollection LocallyRingedSpace.{u} := ⟨LocallyRingedSpace.empty⟩

/-- The canonical map from the empty locally ringed space. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.emptyTo** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.LocallyRingedSpace`。
形式化陈述：emptyTo (X : LocallyRingedSpace.{u}) : ∅ ⟶ X
参数：X : LocallyRingedSpace.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the empty locally ringed space.
-/
def emptyTo (X : LocallyRingedSpace.{u}) : ∅ ⟶ X :=
  ⟨⟨ofHom ⟨fun x => PEmpty.elim x, by fun_prop⟩,
    { app := fun U => CommRingCat.ofHom <| by refine ⟨⟨⟨0, ?_⟩, ?_⟩, ?_, ?_⟩ <;> intros <;> rfl }⟩,
    fun x => PEmpty.elim x⟩

noncomputable
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : LocallyRingedSpace.{u}} : Unique (∅ ⟶ X) where
  default := LocallyRingedSpace.emptyTo X
  uniq f := by ext ⟨⟩ x; cat_disch

/-- The empty space is initial in `LocallyRingedSpace`. -/
noncomputable
/-
**AlgebraicGeometry.LocallyRingedSpace.emptyIsInitial** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：emptyIsInitial : Limits.IsInitial (∅ : LocallyRingedSpace.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def emptyIsInitial : Limits.IsInitial (∅ : LocallyRingedSpace.{u}) := Limits.IsInitial.ofUnique _

-- This actually holds for all ringed spaces with nontrivial stalks.
/-
**AlgebraicGeometry.LocallyRingedSpace.basicOpen_zero** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：basicOpen_zero (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) : X.toRi
ngedSpace.basicOpen (0 : X.presheaf.obj <| op U) = ⊥
参数：X : LocallyRingedSpace.{u}；U : Opens X.carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `isUnit_zero_iff`：isUnit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
-/
theorem basicOpen_zero (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) :
    X.toRingedSpace.basicOpen (0 : X.presheaf.obj <| op U) = ⊥ := by
  ext x
  simp only [RingedSpace.basicOpen, Opens.coe_mk, Set.mem_ofPred_eq,
    Opens.coe_bot, Set.mem_empty_iff_false,
    iff_false, not_exists]
  intro hx
  rw [map_zero, isUnit_zero_iff]
  change (0 : X.presheaf.stalk x) ≠ (1 : X.presheaf.stalk x)
  exact zero_ne_one

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.basicOpen_eq_bot_of_isNilpotent** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：basicOpen_eq_bot_of_isNilpotent (X : LocallyRingedSpace.{u}) (U : Opens X.
carrier) (f : (X.presheaf.obj <| op U)) (hf : IsNilpotent f) : X.toRingedSpace.b
asicOpen f = ⊥
参数：X : LocallyRingedSpace.{u}；U : Opens X.carrier；f : (X.presheaf.obj <| op U)；h
f : IsNilpotent f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_zero_of_zero_eq_one`：eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M
₀) : a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.basicOpen_zero`：basicOpen_zero (X :
 LocallyRingedSpace.{u}) (U : Opens X.carrier) : X.toRingedSpace.basicOpen (0 : 
X.presheaf.obj <| op U) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.RingedSpace.basicOpen_pow`：basicOpen_pow {U : Opens X}
 (f : X.presheaf.obj (op U)) (n : Nat) (h : 0 < n) : X.basicOpen (f ^ n) = X.bas
icOpen f
-/
lemma basicOpen_eq_bot_of_isNilpotent (X : LocallyRingedSpace.{u}) (U : Opens X.carrier)
    (f : (X.presheaf.obj <| op U)) (hf : IsNilpotent f) :
    X.toRingedSpace.basicOpen f = ⊥ := by
  obtain ⟨n, hn⟩ := hf
  cases n.eq_zero_or_pos with
  | inr h =>
    rw [← X.toRingedSpace.basicOpen_pow f n h, hn]
    simp [basicOpen_zero]
  | inl h =>
    rw [h, pow_zero] at hn
    simp [eq_zero_of_zero_eq_one hn.symm f, basicOpen_zero]
/-
**AlgebraicGeometry.LocallyRingedSpace.component_nontrivial** 是 Mathlib 中的一个实例，位
于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：component_nontrivial (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) [h
U : Nonempty U] : Nontrivial (X.presheaf.obj <| op U)
参数：X : LocallyRingedSpace.{u}；U : Opens X.carrier。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
-/
instance component_nontrivial (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) [hU : Nonempty U] :
    Nontrivial (X.presheaf.obj <| op U) :=
  (X.presheaf.germ _ _ hU.some.2).hom.domain_nontrivial

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.iso_hom_base_inv_base** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：iso_hom_base_inv_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) : e.hom.b
ase ≫ e.inv.base = 𝟙 _
参数：e : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iso_hom_base_inv_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) :
    e.hom.base ≫ e.inv.base = 𝟙 _ := by
  simp only [← comp_base, Iso.hom_inv_id, id_toHom, PresheafedSpace.id_base]

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.iso_hom_base_inv_base_apply** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：iso_hom_base_inv_base_apply {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (x 
: X) : (e.inv.base (e.hom.base x)) = x
参数：e : X ≅ Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.iso_hom_base_inv_base`：iso_hom_base
_inv_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) : e.hom.base ≫ e.inv.base =
 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iso_hom_base_inv_base_apply {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (x : X) :
    (e.inv.base (e.hom.base x)) = x := by
  change (e.hom.base ≫ e.inv.base) x = 𝟙 X.toPresheafedSpace x
  simp

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.iso_inv_base_hom_base** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：iso_inv_base_hom_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) : e.inv.b
ase ≫ e.hom.base = 𝟙 _
参数：e : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iso_inv_base_hom_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) :
    e.inv.base ≫ e.hom.base = 𝟙 _ := by
  simp only [← comp_base, Iso.inv_hom_id, id_toHom, PresheafedSpace.id_base]

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.iso_inv_base_hom_base_apply** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：iso_inv_base_hom_base_apply {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (y 
: Y) : (e.hom.base (e.inv.base y)) = y
参数：e : X ≅ Y；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.iso_inv_base_hom_base`：iso_inv_base
_hom_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) : e.inv.base ≫ e.hom.base =
 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iso_inv_base_hom_base_apply {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (y : Y) :
    (e.hom.base (e.inv.base y)) = y := by
  change (e.inv.base ≫ e.hom.base) y = 𝟙 Y.toPresheafedSpace y
  simp

section Stalks

variable {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.stalkMap_id** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.LocallyRingedSpace`。
形式化陈述：stalkMap_id (X : LocallyRingedSpace.{u}) (x : X) : (𝟙 X : X ⟶ X).stalkMap 
x = 𝟙 (X.presheaf.stalk x)
参数：X : LocallyRingedSpace.{u}；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap.id`：id (X : PresheafedSpace.{
_, _, v} C) (x : X) : (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x)
-/
lemma stalkMap_id (X : LocallyRingedSpace.{u}) (x : X) :
    (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x) :=
  PresheafedSpace.stalkMap.id _ x
/-
**AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：stalkMap_comp (x : X) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap (f.base x)
 ≫ f.stalkMap x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap.comp`：comp {X Y Z : Presheafe
dSpace.{_, _, v} C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) : (α ≫ β).stalkMap x = (β.st
alkMap (α.base x) : Z.presheaf.stalk …
-/
lemma stalkMap_comp (x : X) :
    (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap (f.base x) ≫ f.stalkMap x :=
  PresheafedSpace.stalkMap.comp f.toHom g.toHom x

@[reassoc]
/-
**AlgebraicGeometry.LocallyRingedSpace.stalkSpecializes_stalkMap** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：stalkSpecializes_stalkMap (x x' : X) (h : x ⤳ x') : Y.presheaf.stalkSpecia
lizes (f.base.hom.map_specializes h) ≫ f.stalkMap x = f.stalkMap x' ≫ X.presheaf
.stalkSpecializes h
参数：x x' : X；h : x ⤳ x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap.stalkSpecializes_stalkMap`：st
alkSpecializes_stalkMap {X Y : PresheafedSpace.{_, _, v} C} (f : X ⟶ Y) {x y : X
} (h : x ⤳ y) : Y.presheaf.stalkSpecializes (f.base.hom.ma…
-/
lemma stalkSpecializes_stalkMap (x x' : X) (h : x ⤳ x') :
    Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) ≫ f.stalkMap x =
      f.stalkMap x' ≫ X.presheaf.stalkSpecializes h :=
  PresheafedSpace.stalkMap.stalkSpecializes_stalkMap f.toHom h
/-
**AlgebraicGeometry.LocallyRingedSpace.stalkSpecializes_stalkMap_apply** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：stalkSpecializes_stalkMap_apply (x x' : X) (h : x ⤳ x') (y) : f.stalkMap x
 (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) y) = (X.presheaf.st
alkSpecializes h (f.stalkMap x' y))
参数：x x' : X；h : x ⤳ x'；y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `ContinuousMap.map_specializes`：map_specializes (f : C(α, β)) {x y : α} (
h : x ⤳ y) : f x ⤳ f y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CommRingCat.hom_ext_iff`：∀ {R S : CommRingCat} {f g : R ⟶ S}, f = g ↔ Co
mmRingCat.Hom.hom f = CommRingCat.Hom.hom g
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkSpecializes_stalkMap`：stalkSpe
cializes_stalkMap (x x' : X) (h : x ⤳ x') : Y.presheaf.stalkSpecializes (f.base.
hom.map_specializes h) ≫ f.stalkMap x = f.stalkMap x…
-/
lemma stalkSpecializes_stalkMap_apply (x x' : X) (h : x ⤳ x') (y) :
    f.stalkMap x (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) y) =
      (X.presheaf.stalkSpecializes h (f.stalkMap x' y)) :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkSpecializes_stalkMap f x x' h)) y

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：stalkMap_congr (f g : X ⟶ Y) (hfg : f = g) (x x' : X) (hxx' : x = x') : f.
stalkMap x ≫ X.presheaf.stalkSpecializes (specializes_of_eq hxx'.symm) = Y.presh
eaf.stalkSpecializes (specializes_of_eq <| hfg ▸ hxx' ▸ rfl) ≫ g.stalkMap x'
参数：f g : X ⟶ Y；hfg : f = g；x x' : X；hxx' : x = x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `specializes_of_eq`：specializes_of_eq (e : x = y) : x ⤳ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.stalkSpecializes_refl`：stalkSpecializes_refl (F : X.Pres
heaf C) (x : X) : F.stalkSpecializes (specializes_refl x) = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma stalkMap_congr (f g : X ⟶ Y) (hfg : f = g) (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ X.presheaf.stalkSpecializes (specializes_of_eq hxx'.symm) =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| hfg ▸ hxx' ▸ rfl) ≫ g.stalkMap x' := by
  subst hfg
  subst hxx'
  simp

@[reassoc]
/-
**AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr_hom** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：stalkMap_congr_hom (f g : X ⟶ Y) (hfg : f = g) (x : X) : f.stalkMap x = Y.
presheaf.stalkSpecializes (specializes_of_eq <| hfg ▸ rfl) ≫ g.stalkMap x
参数：f g : X ⟶ Y；hfg : f = g；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `specializes_of_eq`：specializes_of_eq (e : x = y) : x ⤳ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopCat.Presheaf.stalkSpecializes_refl`：stalkSpecializes_refl (F : X.Pres
heaf C) (x : X) : F.stalkSpecializes (specializes_refl x) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma stalkMap_congr_hom (f g : X ⟶ Y) (hfg : f = g) (x : X) :
    f.stalkMap x = Y.presheaf.stalkSpecializes (specializes_of_eq <| hfg ▸ rfl) ≫
      g.stalkMap x := by
  subst hfg
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr_point** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：stalkMap_congr_point {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x x' : X)
 (hxx' : x = x') : f.stalkMap x ≫ X.presheaf.stalkSpecializes (specializes_of_eq
 hxx'.symm) = Y.presheaf.stalkSpecializes (specializes_of_eq <| hxx' ▸ rfl) ≫ f.
stalkMap x'
参数：f : X ⟶ Y；x x' : X；hxx' : x = x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `specializes_of_eq`：specializes_of_eq (e : x = y) : x ⤳ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.stalkSpecializes_refl`：stalkSpecializes_refl (F : X.Pres
heaf C) (x : X) : F.stalkSpecializes (specializes_refl x) = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma stalkMap_congr_point {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ X.presheaf.stalkSpecializes (specializes_of_eq hxx'.symm) =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| hxx' ▸ rfl) ≫ f.stalkMap x' := by
  subst hxx'
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.LocallyRingedSpace.stalkMap_hom_inv** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：stalkMap_hom_inv (e : X ≅ Y) (y : Y) : e.hom.stalkMap (e.inv.base y) ≫ e.i
nv.stalkMap y = Y.presheaf.stalkSpecializes (specializes_of_eq <| by simp)
参数：e : X ≅ Y；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `specializes_of_eq`：specializes_of_eq (e : x = y) : x ⤳ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp`：stalkMap_comp (x : X
) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap (f.base x) ≫ f.stalkMap x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr_hom`：stalkMap_congr_
hom (f g : X ⟶ Y) (hfg : f = g) (x : X) : f.stalkMap x = Y.presheaf.stalkSpecial
izes (specializes_of_eq <| hfg ▸ rfl) ≫ g.sta…
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_id`：stalkMap_id (X : Local
lyRingedSpace.{u}) (x : X) : (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma stalkMap_hom_inv (e : X ≅ Y) (y : Y) :
    e.hom.stalkMap (e.inv.base y) ≫ e.inv.stalkMap y =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| by simp) := by
  rw [← stalkMap_comp, LocallyRingedSpace.stalkMap_congr_hom (e.inv ≫ e.hom) (𝟙 _) (by simp)]
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.stalkMap_hom_inv_apply** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：stalkMap_hom_inv_apply (e : X ≅ Y) (y : Y) (z) : e.inv.stalkMap y (e.hom.s
talkMap (e.inv.base y) z) = Y.presheaf.stalkSpecializes (specializes_of_eq <| by
 simp) z
参数：e : X ≅ Y；y : Y；z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `specializes_of_eq`：specializes_of_eq (e : x = y) : x ⤳ y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CommRingCat.hom_ext_iff`：∀ {R S : CommRingCat} {f g : R ⟶ S}, f = g ↔ Co
mmRingCat.Hom.hom f = CommRingCat.Hom.hom g
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_hom_inv`：stalkMap_hom_inv 
(e : X ≅ Y) (y : Y) : e.hom.stalkMap (e.inv.base y) ≫ e.inv.stalkMap y = Y.presh
eaf.stalkSpecializes (specializes_of_eq <| …
-/
lemma stalkMap_hom_inv_apply (e : X ≅ Y) (y : Y) (z) :
    e.inv.stalkMap y (e.hom.stalkMap (e.inv.base y) z) =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| by simp) z :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_hom_inv e y)) z

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.LocallyRingedSpace.stalkMap_inv_hom** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：stalkMap_inv_hom (e : X ≅ Y) (x : X) : e.inv.stalkMap (e.hom.base x) ≫ e.h
om.stalkMap x = X.presheaf.stalkSpecializes (specializes_of_eq <| by simp)
参数：e : X ≅ Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `specializes_of_eq`：specializes_of_eq (e : x = y) : x ⤳ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp`：stalkMap_comp (x : X
) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap (f.base x) ≫ f.stalkMap x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr_hom`：stalkMap_congr_
hom (f g : X ⟶ Y) (hfg : f = g) (x : X) : f.stalkMap x = Y.presheaf.stalkSpecial
izes (specializes_of_eq <| hfg ▸ rfl) ≫ g.sta…
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_id`：stalkMap_id (X : Local
lyRingedSpace.{u}) (x : X) : (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma stalkMap_inv_hom (e : X ≅ Y) (x : X) :
    e.inv.stalkMap (e.hom.base x) ≫ e.hom.stalkMap x =
      X.presheaf.stalkSpecializes (specializes_of_eq <| by simp) := by
  rw [← stalkMap_comp, LocallyRingedSpace.stalkMap_congr_hom (e.hom ≫ e.inv) (𝟙 _) (by simp)]
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.stalkMap_inv_hom_apply** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：stalkMap_inv_hom_apply (e : X ≅ Y) (x : X) (y) : e.hom.stalkMap x (e.inv.s
talkMap (e.hom.base x) y) = X.presheaf.stalkSpecializes (specializes_of_eq <| by
 simp) y
参数：e : X ≅ Y；x : X；y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `specializes_of_eq`：specializes_of_eq (e : x = y) : x ⤳ y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CommRingCat.hom_ext_iff`：∀ {R S : CommRingCat} {f g : R ⟶ S}, f = g ↔ Co
mmRingCat.Hom.hom f = CommRingCat.Hom.hom g
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_inv_hom`：stalkMap_inv_hom 
(e : X ≅ Y) (x : X) : e.inv.stalkMap (e.hom.base x) ≫ e.hom.stalkMap x = X.presh
eaf.stalkSpecializes (specializes_of_eq <| …
-/
lemma stalkMap_inv_hom_apply (e : X ≅ Y) (x : X) (y) :
    e.hom.stalkMap x (e.inv.stalkMap (e.hom.base x) y) =
      X.presheaf.stalkSpecializes (specializes_of_eq <| by simp) y :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_inv_hom e x)) y

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.LocallyRingedSpace.stalkMap_germ** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：stalkMap_germ (U : Opens Y) (x : X) (hx : f.base x in U) : Y.presheaf.germ
 U (f.base x) hx ≫ f.stalkMap x = f.c.app (op U) ≫ X.presheaf.germ ((Opens.map f
.base).obj U) x hx
参数：U : Opens Y；x : X；hx : f.base x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap_germ`：stalkMap_germ {X Y : Pr
esheafedSpace.{_, _, v} C} (α : X ⟶ Y) (U : Opens Y) (x : X) (hx : α x in U) : Y
.presheaf.germ U (α x) hx ≫ α.stalkMa…
-/
lemma stalkMap_germ (U : Opens Y) (x : X) (hx : f.base x ∈ U) :
    Y.presheaf.germ U (f.base x) hx ≫ f.stalkMap x =
      f.c.app (op U) ≫ X.presheaf.germ ((Opens.map f.base).obj U) x hx :=
  PresheafedSpace.stalkMap_germ f.toHom U x hx
/-
**AlgebraicGeometry.LocallyRingedSpace.stalkMap_germ_apply** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：stalkMap_germ_apply (U : Opens Y) (x : X) (hx : f.base x in U) (y) : f.sta
lkMap x (Y.presheaf.germ U (f.base x) hx y) = X.presheaf.germ ((Opens.map f.base
).obj U) x hx (f.c.app (op U) y)
参数：U : Opens Y；x : X；hx : f.base x in U；y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColim
its C]   {X Y : AlgebraicGeometry.Presheafe…
-/
lemma stalkMap_germ_apply (U : Opens Y) (x : X) (hx : f.base x ∈ U) (y) :
    f.stalkMap x (Y.presheaf.germ U (f.base x) hx y) =
      X.presheaf.germ ((Opens.map f.base).obj U) x hx (f.c.app (op U) y) :=
  PresheafedSpace.stalkMap_germ_apply f.toHom U x hx y

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.LocallyRingedSpace.preimage_basicOpen** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：preimage_basicOpen {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) {U : Opens Y
} (s : Y.presheaf.obj (op U)) : (Opens.map f.base).obj (Y.toRingedSpace.basicOpe
n s) = @RingedSpace.basicOpen X.toRingedSpace ((Opens.map f.base).obj U) (f.c.ap
p _ s)
参数：f : X ⟶ Y；s : Y.presheaf.obj (op U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `AlgebraicGeometry.RingedSpace.mem_basicOpen`：mem_basicOpen {U : Opens X}
 (f : X.presheaf.obj (op U)) (x : X) (hx : x in U) : x in X.basicOpen f ↔ IsUnit
 (X.presheaf.germ U x hx f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_germ_apply`：stalkMap_germ_
apply (U : Opens Y) (x : X) (hx : f.base x in U) (y) : f.stalkMap x (Y.presheaf.
germ U (f.base x) hx y) = X.presheaf.germ ((Op…
· 使用定理 `RingHom.isUnit_map`：isUnit_map (f : α ->+* β) {a : α} : IsUnit a -> IsUn
it (f a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.isLocalHomValStalkMap`：isLocalHomVa
lStalkMap {X Y : LocallyRingedSpace.{u}} (f : Hom X Y) (x : X) : IsLocalHom (f.s
talkMap x).hom
-/
theorem preimage_basicOpen {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) {U : Opens Y}
    (s : Y.presheaf.obj (op U)) :
    (Opens.map f.base).obj (Y.toRingedSpace.basicOpen s) =
      @RingedSpace.basicOpen X.toRingedSpace ((Opens.map f.base).obj U) (f.c.app _ s) := by
  ext x
  constructor
  · rintro ⟨hxU, hx⟩
    rw [SetLike.mem_coe, X.toRingedSpace.mem_basicOpen _ _ hxU]
    delta toRingedSpace
    rw [← stalkMap_germ_apply]
    exact (f.stalkMap _).hom.isUnit_map hx
  · rintro ⟨hxU, hx⟩
    simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, toRingedSpace] at hx ⊢
    rw [RingedSpace.mem_basicOpen _ s (f.base x) hxU]
    rw [← stalkMap_germ_apply] at hx
    exact (isUnit_map_iff (f.stalkMap x).hom _).mp hx

variable {U : TopCat.{u}} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f)
  (V : Opens U) (x : U) (hx : x ∈ V)

/-- For an open embedding `f : U ⟶ X` and a point `x : U`, we get an isomorphism between the stalk
of `X` at `f x` and the stalk of the restriction of `X` along `f` at `x`. -/
noncomputable
/-
**AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso** 是 Mathlib 中的一个定义，位于命名空
间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：restrictStalkIso : (X.restrict h).presheaf.stalk x ≅ X.presheaf.stalk (f x
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def restrictStalkIso : (X.restrict h).presheaf.stalk x ≅ X.presheaf.stalk (f x) :=
  X.toPresheafedSpace.restrictStalkIso h x

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso_hom_eq_germ** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：restrictStalkIso_hom_eq_germ : (X.restrict h).presheaf.germ _ x hx ≫ (X.re
strictStalkIso h x).hom = X.presheaf.germ (h.functor.obj V) (f x) ⟨x, hx, rfl⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ`：restrict
StalkIso_hom_eq_germ {U : TopCat.{v}} (X : PresheafedSpace.{_, _, v} C) {f : U ⟶
 (X : TopCat.{v})} (h : IsOpenEmbedding f) (V : Open…
-/
lemma restrictStalkIso_hom_eq_germ :
    (X.restrict h).presheaf.germ _ x hx ≫ (X.restrictStalkIso h x).hom =
      X.presheaf.germ (h.functor.obj V) (f x) ⟨x, hx, rfl⟩ :=
  PresheafedSpace.restrictStalkIso_hom_eq_germ X.toPresheafedSpace h V x hx
/-
**AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso_hom_eq_germ_apply** 是 Ma
thlib 中的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：restrictStalkIso_hom_eq_germ_apply (y) : (X.restrictStalkIso h x).hom ((X.
restrict h).presheaf.germ _ x hx y) = X.presheaf.germ (h.functor.obj V) (f x) ⟨x
, hx, rfl⟩ y
参数：y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ_apply`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.
Limits.HasColimits C] {U : TopCat}   (X : AlgebraicGeometr…
-/
lemma restrictStalkIso_hom_eq_germ_apply (y) :
    (X.restrictStalkIso h x).hom ((X.restrict h).presheaf.germ _ x hx y) =
      X.presheaf.germ (h.functor.obj V) (f x) ⟨x, hx, rfl⟩ y :=
  PresheafedSpace.restrictStalkIso_hom_eq_germ_apply X.toPresheafedSpace h V x hx y

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso_inv_eq_germ** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：restrictStalkIso_inv_eq_germ : X.presheaf.germ (h.functor.obj V) (f x) ⟨x,
 hx, rfl⟩ ≫ (X.restrictStalkIso h x).inv = (X.restrict h).presheaf.germ _ x hx
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.restrictStalkIso_inv_eq_germ`：restrict
StalkIso_inv_eq_germ {U : TopCat.{v}} (X : PresheafedSpace.{_, _, v} C) {f : U ⟶
 (X : TopCat.{v})} (h : IsOpenEmbedding f) (V : Open…
-/
lemma restrictStalkIso_inv_eq_germ :
    X.presheaf.germ (h.functor.obj V) (f x) ⟨x, hx, rfl⟩ ≫
      (X.restrictStalkIso h x).inv = (X.restrict h).presheaf.germ _ x hx :=
  PresheafedSpace.restrictStalkIso_inv_eq_germ X.toPresheafedSpace h V x hx
/-
**AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso_inv_eq_germ_apply** 是 Ma
thlib 中的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：restrictStalkIso_inv_eq_germ_apply (y) : (X.restrictStalkIso h x).inv (X.p
resheaf.germ (h.functor.obj V) (f x) ⟨x, hx, rfl⟩ y) = (X.restrict h).presheaf.g
erm _ x hx y
参数：y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.restrictStalkIso_inv_eq_germ_apply`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.
Limits.HasColimits C] {U : TopCat}   (X : AlgebraicGeometr…
-/
lemma restrictStalkIso_inv_eq_germ_apply (y) :
    (X.restrictStalkIso h x).inv
      (X.presheaf.germ (h.functor.obj V) (f x) ⟨x, hx, rfl⟩ y) =
        (X.restrict h).presheaf.germ _ x hx y :=
  PresheafedSpace.restrictStalkIso_inv_eq_germ_apply X.toPresheafedSpace h V x hx y
/-
**AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso_inv_eq_ofRestrict** 是 Ma
thlib 中的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：restrictStalkIso_inv_eq_ofRestrict : (X.restrictStalkIso h x).inv = (X.ofR
estrict h).stalkMap x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict`：re
strictStalkIso_inv_eq_ofRestrict {U : TopCat.{v}} (X : PresheafedSpace.{_, _, v}
 C) {f : U ⟶ (X : TopCat.{v})} (h : IsOpenEmbedding f) (x …
-/
lemma restrictStalkIso_inv_eq_ofRestrict :
    (X.restrictStalkIso h x).inv = (X.ofRestrict h).stalkMap x :=
  PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict X.toPresheafedSpace h x
/-
**AlgebraicGeometry.LocallyRingedSpace.ofRestrict_stalkMap_isIso** 是 Mathlib 中的一
个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：ofRestrict_stalkMap_isIso : IsIso ((X.ofRestrict h).stalkMap x)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ofRestrict_stalkMap_isIso : IsIso ((X.ofRestrict h).stalkMap x) :=
  PresheafedSpace.ofRestrict_stalkMap_isIso X.toPresheafedSpace h x

end Stalks

end LocallyRingedSpace

end AlgebraicGeometry

