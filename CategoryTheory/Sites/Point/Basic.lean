/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Points of a site

Let `C` be a category equipped with a Grothendieck topology `J`. In this file,
we define the notion of point of the site `(C, J)`, as a
structure `GrothendieckTopology.Point`. Such a `Φ : J.Point` consists
in a functor `Φ.fiber : C ⥤ Type w` such that the category `Φ.fiber.Elements`
is cofiltered (and initially small) and such that if `x : Φ.fiber.obj X`
and `R` is a covering sieve of `X`, then `x` belongs to the image
of some `y : Φ.fiber.obj Y` by a morphism `f : Y ⟶ X` which belongs to `R`.
(This definition is essentially the definition of a fiber functor on a site
from SGA 4 IV 6.3.)

The fact that `Φ.fiber.Elementsᵒᵖ` is filtered allows to define
`Φ.presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A` by taking the filtering colimit
of the evaluation functors at `op X` when `(X : C, x : F.obj X)` varies in
`Φ.fiber.Elementsᵒᵖ`. We define `Φ.sheafFiber : Sheaf J A ⥤ A` as the
restriction of `Φ.presheafFiber` to the full subcategory of sheaves.

Under certain assumptions, we show that if `A` is concrete and
`P ⟶ Q` is a locally bijective morphism between presheaves,
then the induced morphism on fibers is a bijection. It follows
that not only `Φ.sheafFiber : Sheaf J A ⥤ A` is the restriction of
`Φ.presheafFiber` but it may also be thought as a localization
of this functor with respect to the class of morphisms `J.W`.
In particular, the fiber of a presheaf identifies to the fiber of
its associated sheaf.

Under suitable assumptions on the target category `A`, we show that
both `Φ.presheafFiber` and `Φ.sheafFiber` commute with finite limits
and with arbitrary colimits. (The commutation of `Φ.sheafFiber` with colimits
is obtained in the file `Mathlib/CategoryTheory/Sites/Point/Skyscraper.lean`.)

-/

@[expose] public section

universe w' w v v' v'' u u' u''

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

namespace GrothendieckTopology

variable (J : GrothendieckTopology C)

/-- Given `J` a Grothendieck topology on a category `C`, a point of the site `(C, J)`
consists of a functor `fiber : C ⥤ Type w` such that the category `fiber.Elements`
is initially small (which allows defining the fiber functor on presheaves by
taking colimits) and cofiltered (so that the fiber functor on presheaves is exact),
and such that covering sieves induce jointly surjective maps on fibers (which
allows to show that the fibers of a presheaf and its associated sheaf are isomorphic). -/
/-
**CategoryTheory.GrothendieckTopology.Point** 是 Mathlib 中的一个结构，位于命名空间 `CategoryT
heory.GrothendieckTopology`。
形式化陈述：Point where /-- the fiber functor on the underlying category of the site -
/ fiber : C ⥤ Type w isCofiltered : IsCofiltered fiber.Elements
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `J` a Grothendieck topology on a category `C`, a point of the site `(C, J)
`
consists of a functor `fiber : C ⥤ Type w` such that the category `fiber.Element
s`
is initially small (which allows defining the fiber functor on presheaves by
taking colimits) and cofiltered (so that the fiber functor on presheaves is exac
t),
and such that covering sieves induce jointly surjective maps on fibers (which
allows to show that the fibers of a presheaf and its associated sheaf are isomor
phic).
-/
structure Point where
  /-- the fiber functor on the underlying category of the site -/
  fiber : C ⥤ Type w
  isCofiltered : IsCofiltered fiber.Elements := by infer_instance
  initiallySmall : InitiallySmall.{w} fiber.Elements := by infer_instance
  jointly_surjective {X : C} (R : Sieve X) (h : R ∈ J X) (x : fiber.obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x

namespace Point

attribute [instance] initiallySmall isCofiltered

variable {J} (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]
  {B : Type u''} [Category.{v''} B]
  [HasColimitsOfSize.{w, w} A] [HasColimitsOfSize.{w, w} B]

/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasColimitsOfShape Φ.fiber.Elementsᵒᵖ A :=
  hasColimitsOfShape_of_finallySmall _ _
/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSifted Φ.fiber.Elementsᵒᵖ := IsFiltered.isSifted
/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallySmall.{w} C] [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
    HasExactColimitsOfShape Φ.fiber.Elementsᵒᵖ A :=
  hasExactColimitsOfShape_of_final _
    (FinallySmall.fromFilteredFinalModel Φ.fiber.Elementsᵒᵖ)

/-- The fiber functor on categories of presheaves that is given by a point of a site. -/
/-
**CategoryTheory.GrothendieckTopology.Point.presheafFiber** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instHasColimitsOfShapeOpposite
ElementsFiber`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Cat
egoryTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…

--- 原说明 ---
The fiber functor on categories of presheaves that is given by a point of a site
.
-/
noncomputable def presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A :=
  (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π Φ.fiber).op ⋙ colim

/-- Given a point `Φ` of a site `(C, J)`, `X : C` and `x : Φ.fiber.obj X`, this
is the canonical map `P.obj (op X) ⟶ Φ.presheafFiber.obj P`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiber** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiber (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) : P.obj (op X) ⟶
 Φ.presheafFiber.obj P
参数：X : C；x : Φ.fiber.obj X；P : Cᵒᵖ ⥤ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a point `Φ` of a site `(C, J)`, `X : C` and `x : Φ.fiber.obj X`, this
is the canonical map `P.obj (op X) ⟶ Φ.presheafFiber.obj P`.
-/
noncomputable def toPresheafFiber (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    P.obj (op X) ⟶ Φ.presheafFiber.obj P :=
  colimit.ι ((CategoryOfElements.π Φ.fiber).op ⋙ P) (op ⟨X, x⟩)

@[ext]
/-
**CategoryTheory.GrothendieckTopology.Point.presheafFiber_hom_ext** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：presheafFiber_hom_ext {P : Cᵒᵖ ⥤ A} {T : A} {f g : Φ.presheafFiber.obj P ⟶
 T} (h : forall (X : C) (x : Φ.fiber.obj X), Φ.toPresheafFiber X x P ≫ f = Φ.toP
resheafFiber X x P ≫ g) : f = g
参数：h : forall (X : C) (x : Φ.fiber.obj X), Φ.toPresheafFiber X x P ≫ f = Φ.toPre
sheafFiber X x P ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instHasColimitsOfShapeOpposite
ElementsFiber`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Cat
egoryTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
-/
lemma presheafFiber_hom_ext
    {P : Cᵒᵖ ⥤ A} {T : A} {f g : Φ.presheafFiber.obj P ⟶ T}
    (h : ∀ (X : C) (x : Φ.fiber.obj X), Φ.toPresheafFiber X x P ≫ f =
      Φ.toPresheafFiber X x P ≫ g) : f = g :=
  colimit.hom_ext (by rintro ⟨⟨X, x⟩⟩; exact h X x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a point `Φ` of a site `(C, J)`, `X : C` and `x : Φ.fiber.obj X`,
this is the map `P.obj (op X) ⟶ Φ.presheafFiber.obj P` for any `P : Cᵒᵖ ⥤ A`
as a natural transformation. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiberNatTrans** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiberNatTrans (X : C) (x : Φ.fiber.obj X) : (evaluation Cᵒᵖ A).o
bj (op X) ⟶ Φ.presheafFiber where app
参数：X : C；x : Φ.fiber.obj X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a point `Φ` of a site `(C, J)`, `X : C` and `x : Φ.fiber.obj X`,
this is the map `P.obj (op X) ⟶ Φ.presheafFiber.obj P` for any `P : Cᵒᵖ ⥤ A`
as a natural transformation.
-/
noncomputable def toPresheafFiberNatTrans (X : C) (x : Φ.fiber.obj X) :
    (evaluation Cᵒᵖ A).obj (op X) ⟶ Φ.presheafFiber where
  app := Φ.toPresheafFiber X x
  naturality _ _ f := by simp [presheafFiber, toPresheafFiber]

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_w** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiber_w {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) 
: P.map f.op ≫ Φ.toPresheafFiber X x P = Φ.toPresheafFiber Y (Φ.fiber.map f x) P
参数：f : X ⟶ Y；x : Φ.fiber.obj X；P : Cᵒᵖ ⥤ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.w`：∀ {J : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   
(F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instHasColimitsOfShapeOpposite
ElementsFiber`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Cat
egoryTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
-/
lemma toPresheafFiber_w {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    P.map f.op ≫ Φ.toPresheafFiber X x P =
      Φ.toPresheafFiber Y (Φ.fiber.map f x) P :=
  colimit.w ((CategoryOfElements.π Φ.fiber).op ⋙ P)
      (CategoryOfElements.homMk ⟨X, x⟩ ⟨Y, Φ.fiber.map f x⟩ f rfl).op

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiber_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fibe
r.obj X) : Φ.toPresheafFiber X x P ≫ Φ.presheafFiber.map g = g.app (op X) ≫ Φ.to
PresheafFiber X x Q
参数：g : P ⟶ Q；X : C；x : Φ.fiber.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma toPresheafFiber_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.presheafFiber.map g =
      g.app (op X) ≫ Φ.toPresheafFiber X x Q :=
  ((Φ.toPresheafFiberNatTrans X x).naturality g).symm

set_option backward.defeqAttrib.useBackward true in
/-- The (colimit) cocone which defines the fiber of a presheaf. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Point.presheafFiberCocone** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：presheafFiberCocone (P : Cᵒᵖ ⥤ A) : Cocone ((CategoryOfElements.π Φ.fiber)
.op ⋙ P) where pt
参数：P : Cᵒᵖ ⥤ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (colimit) cocone which defines the fiber of a presheaf.
-/
noncomputable def presheafFiberCocone (P : Cᵒᵖ ⥤ A) :
    Cocone ((CategoryOfElements.π Φ.fiber).op ⋙ P) where
  pt := Φ.presheafFiber.obj P
  ι.app x := Φ.toPresheafFiber x.unop.1 x.unop.2 P

/-- The cocone `Φ.presheafFiberCocone P` is a colimit. -/
/-
**CategoryTheory.GrothendieckTopology.Point.isColimitPresheafFiberCocone** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：isColimitPresheafFiberCocone (P : Cᵒᵖ ⥤ A) : IsColimit (Φ.presheafFiberCoc
one P)
参数：P : Cᵒᵖ ⥤ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone `Φ.presheafFiberCocone P` is a colimit.
-/
noncomputable def isColimitPresheafFiberCocone (P : Cᵒᵖ ⥤ A) :
    IsColimit (Φ.presheafFiberCocone P) :=
  colimit.isColimit _

/-- The isomorphism `shrinkYoneda.{w} ⋙ Φ.presheafFiber ≅ Φ.fiber`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.shrinkYonedaCompPresheafFiberIso** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：shrinkYonedaCompPresheafFiberIso [LocallySmall.{w} C] : shrinkYoneda.{w} ⋙
 Φ.presheafFiber ≅ Φ.fiber
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `shrinkYoneda.{w} ⋙ Φ.presheafFiber ≅ Φ.fiber`.
-/
noncomputable def shrinkYonedaCompPresheafFiberIso [LocallySmall.{w} C] :
    shrinkYoneda.{w} ⋙ Φ.presheafFiber ≅ Φ.fiber :=
  Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso _
/-
**CategoryTheory.GrothendieckTopology.Point.shrinkYonedaCompPresheafFiberIso_inv
_app_toPresheafFiber** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopol
ogy.Point`。
形式化陈述：shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber [LocallySmall.{w}
 C] {X : C} (x : Φ.fiber.obj X) : Φ.shrinkYonedaCompPresheafFiberIso.inv.app X x
 = Φ.toPresheafFiber X x (shrinkYoneda.{w}.obj X) (shrinkYonedaObjObjEquiv.symm 
(𝟙 X))
参数：x : Φ.fiber.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompCo
limIso_inv_app_apply`：shrinkYonedaCompWhiskeringLeftObjπCompColimIso_inv_app_app
ly [HasColimitsOfShape F.Elementsᵒᵖ (Type w)] (u : F.Elements) : (shrinkYonedaCo
mp…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instHasColimitsOfShapeOpposite
ElementsFiber`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Cat
egoryTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
-/
lemma shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber
    [LocallySmall.{w} C] {X : C} (x : Φ.fiber.obj X) :
    Φ.shrinkYonedaCompPresheafFiberIso.inv.app X x =
    Φ.toPresheafFiber X x (shrinkYoneda.{w}.obj X)
      (shrinkYonedaObjObjEquiv.symm (𝟙 X)) :=
  Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso_inv_app_apply
    _ (Functor.elementsMk (Φ.fiber) _ x)
/-
**CategoryTheory.GrothendieckTopology.Point.presheafFiber_map_shrinkYoneda_map_s
hrinkYonedaCompPresheafFiberIso_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.GrothendieckTopology.Point`。
形式化陈述：presheafFiber_map_shrinkYoneda_map_shrinkYonedaCompPresheafFiberIso_inv_ap
p [LocallySmall.{w} C] {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) : Φ.presheafFib
er.map (shrinkYoneda.{w}.map f) (Φ.shrinkYonedaCompPresheafFiberIso.inv.app X x)
 = Φ.toPresheafFiber X x (shrinkYoneda.{w}.obj Y) (shrinkYonedaObjObjEquiv.symm 
f)
参数：f : X ⟶ Y；x : Φ.fiber.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.shrinkYonedaCompPresheafFiberI
so_inv_app_toPresheafFiber`：shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafF
iber [LocallySmall.{w} C] {X : C} (x : Φ.fiber.obj X) : Φ.shrinkYonedaCompPreshe
afFiberI…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality_app
ly`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory
.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm`：shrink
Yoneda_map_app_shrinkYonedaObjObjEquiv_symm {X X' : C} {Y : Cᵒᵖ} (f : Y.unop ⟶ X
) (g : X ⟶ X') : (shrinkYoneda.map g).app _ (shrinkYon…
-/
lemma presheafFiber_map_shrinkYoneda_map_shrinkYonedaCompPresheafFiberIso_inv_app
    [LocallySmall.{w} C] {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) :
    Φ.presheafFiber.map (shrinkYoneda.{w}.map f)
      (Φ.shrinkYonedaCompPresheafFiberIso.inv.app X x) =
    Φ.toPresheafFiber X x (shrinkYoneda.{w}.obj Y)
      (shrinkYonedaObjObjEquiv.symm f) := by
  rw [shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber]
  refine (Φ.toPresheafFiber_naturality_apply (shrinkYoneda.{w}.map f) _ x
    (shrinkYonedaObjObjEquiv.symm (𝟙 X))).trans (congr_arg _ ?_)
  simpa using shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w} (𝟙 _) f

section

variable {P : Cᵒᵖ ⥤ A} {T : A}
  (φ : ∀ (X : C) (_ : Φ.fiber.obj X), P.obj (op X) ⟶ T)
  (hφ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : Φ.fiber.obj X),
    P.map f.op ≫ φ X x = φ Y (Φ.fiber.map f x) := by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
/-- Constructor for morphisms from the fiber of a presheaf. -/
/-
**CategoryTheory.GrothendieckTopology.Point.presheafFiberDesc** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：presheafFiberDesc : Φ.presheafFiber.obj P ⟶ T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms from the fiber of a presheaf.
-/
noncomputable def presheafFiberDesc :
    Φ.presheafFiber.obj P ⟶ T :=
  colimit.desc _ (Cocone.mk _ { app x := φ x.unop.1 x.unop.2 })

set_option backward.privateInPublic true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiber_presheafFiberDesc (X : C) (x : Φ.fiber.obj X) : Φ.toPreshe
afFiber X x P ≫ Φ.presheafFiberDesc φ hφ = φ X x
参数：X : C；x : Φ.fiber.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
-/
lemma toPresheafFiber_presheafFiberDesc (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.presheafFiberDesc φ hφ = φ X x :=
  colimit.ι_desc _ _

end

variable {FC : A → A → Type*} {CC : A → Type w'}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w'} A FC]

section

variable {P Q : Cᵒᵖ ⥤ A}

variable [PreservesFilteredColimitsOfSize.{w, w} (forget A)] [LocallySmall.{w} C]

/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesColimitsOfShape Φ.fiber.Elementsᵒᵖ (forget A) :=
  Functor.Final.preservesColimitsOfShape_of_final (FinallySmall.fromFilteredFinalModel.{w} _) _
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_jointly_surjective**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiber_jointly_surjective (p : ToType (Φ.presheafFiber.obj P)) : 
exists (X : C) (x : Φ.fiber.obj X) (z : ToType (P.obj (op X))), Φ.toPresheafFibe
r X x P z = p
参数：p : ToType (Φ.presheafFiber.obj P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instHasColimitsOfShapeOpposite
ElementsFiber`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Cat
egoryTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instPreservesColimitsOfShapeOp
positeElementsFiberForget`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u}
 C] {J : CategoryTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [i
nst_1 :…
-/
lemma toPresheafFiber_jointly_surjective (p : ToType (Φ.presheafFiber.obj P)) :
    ∃ (X : C) (x : Φ.fiber.obj X) (z : ToType (P.obj (op X))),
      Φ.toPresheafFiber X x P z = p := by
  obtain ⟨⟨X, x⟩, z, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) p
  exact ⟨X, x, z, rfl⟩
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_jointly_surjective**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiber_jointly_surjective (p : ToType (Φ.presheafFiber.obj P)) : 
exists (X : C) (x : Φ.fiber.obj X) (z : ToType (P.obj (op X))), Φ.toPresheafFibe
r X x P z = p
参数：p : ToType (Φ.presheafFiber.obj P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instHasColimitsOfShapeOpposite
ElementsFiber`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Cat
egoryTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instPreservesColimitsOfShapeOp
positeElementsFiberForget`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u}
 C] {J : CategoryTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [i
nst_1 :…
-/
lemma toPresheafFiber_jointly_surjective₂ (p₁ p₂ : ToType (Φ.presheafFiber.obj P)) :
    ∃ (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj (op X))),
      Φ.toPresheafFiber X x P z₁ = p₁ ∧ Φ.toPresheafFiber X x P z₂ = p₂ := by
  obtain ⟨⟨X, x⟩, z₁, z₂, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) p₁ p₂
  exact ⟨X, x, z₁, z₂, rfl, rfl⟩
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_eq_iff'** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiber_eq_iff' (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj
 (op X))) : Φ.toPresheafFiber X x P z₁ = Φ.toPresheafFiber X x P z₂ ↔ exists (Y 
: C) (f : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map f y = x ∧ P.map f.op z₁ = P.ma
p f.op z₂
参数：X : C；x : Φ.fiber.obj X；z₁ z₂ : ToType (P.obj (op X))。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instHasColimitsOfShapeOpposite
ElementsFiber`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Cat
egoryTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `CategoryTheory.Limits.IsColimit.eq_iff'`：∀ {J : Type u_1} {C : Type u_2}
 [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Catego
ry.{v_2, u_2} C] {FC : C → C …
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instPreservesColimitsOfShapeOp
positeElementsFiberForget`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u}
 C] {J : CategoryTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [i
nst_1 :…
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.isCofiltered`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} (self : J.Point),   CategoryTheory.IsCo…
-/
lemma toPresheafFiber_eq_iff' (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj (op X))) :
    Φ.toPresheafFiber X x P z₁ = Φ.toPresheafFiber X x P z₂ ↔
      ∃ (Y : C) (f : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map f y = x ∧
        P.map f.op z₁ = P.map f.op z₂ := by
  refine ((colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P)).eq_iff' ..).trans ?_
  constructor
  · rintro ⟨⟨Y, y⟩, ⟨f, hf⟩, hf'⟩
    exact ⟨Y, f, y, hf, hf'⟩
  · rintro ⟨Y, f, y, hf, hf'⟩
    exact ⟨⟨Y, y⟩, ⟨f, hf⟩, hf'⟩

variable (f : P ⟶ Q)
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_map_surjective** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiber_map_surjective [Presheaf.IsLocallySurjective J f] : Functi
on.Surjective (Φ.presheafFiber.map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_jointly_surjec
tive`：toPresheafFiber_jointly_surjective (p : ToType (Φ.presheafFiber.obj P)) : 
exists (X : C) (x : Φ.fiber.obj X) (z : ToType (P.obj (op X))), Φ.…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.jointly_surjective`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckT
opology C} (self : J.Point)   {X : C},   ∀ R ∈ J X…
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality_app
ly`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory
.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toPresheafFiber_map_surjective [Presheaf.IsLocallySurjective J f] :
    Function.Surjective (Φ.presheafFiber.map f) := by
  intro p
  obtain ⟨X, x, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective p
  obtain ⟨Y, g, ⟨t, ht⟩, y, rfl⟩ := Φ.jointly_surjective _ (Presheaf.imageSieve_mem J f z) x
  exact ⟨Φ.toPresheafFiber Y y P t, by simp [← toPresheafFiber_w, ← ht]⟩
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_map_injective** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiber_map_injective [Presheaf.IsLocallyInjective J f] : Function
.Injective (Φ.presheafFiber.map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.jointly_surjective`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckT
opology C} (self : J.Point)   {X : C},   ∀ R ∈ J X…
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_mem`：equalizerSieve_mem [IsLocall
yInjective J φ] {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) 
: equalizerSieve x y in J X.unop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.equalizerSieve_apply`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{
v', u'} D]   {FD : D → D → Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_jointly_surjec
tive₂`：toPresheafFiber_jointly_surjective₂ (p₁ p₂ : ToType (Φ.presheafFiber.obj 
P)) : exists (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj (op…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality_app
ly`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory
.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_w_apply`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Grothend
ieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
-/
lemma toPresheafFiber_map_injective [Presheaf.IsLocallyInjective J f] :
    Function.Injective (Φ.presheafFiber.map f) := by
  suffices ∀ (X : C) (x : Φ.fiber.obj X) (p₁ p₂ : ToType (P.obj (op X)))
      (hp : f.app _ p₁ = f.app _ p₂), Φ.toPresheafFiber X x P p₁ = Φ.toPresheafFiber X x P p₂ by
    rintro q₁ q₂ h
    obtain ⟨X, x, p₁, p₂, rfl, rfl⟩ := Φ.toPresheafFiber_jointly_surjective₂ q₁ q₂
    simp only [toPresheafFiber_naturality_apply, toPresheafFiber_eq_iff'] at h
    obtain ⟨Y, g, y, rfl, h⟩ := h
    simp only [← NatTrans.naturality_apply] at h
    simpa using this _ y _ _ h
  intro X x p₁ p₂ h
  obtain ⟨Y, g, hg, y, rfl⟩ := Φ.jointly_surjective _ (Presheaf.equalizerSieve_mem J f _ _ h) x
  simp_all [← toPresheafFiber_w_apply]
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_map_bijective** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiber_map_bijective [Presheaf.IsLocallyInjective J f] [Presheaf.
IsLocallySurjective J f] : Function.Bijective (Φ.presheafFiber.map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_map_injective`
：toPresheafFiber_map_injective [Presheaf.IsLocallyInjective J f] : Function.Inje
ctive (Φ.presheafFiber.map f)
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_map_surjective
`：toPresheafFiber_map_surjective [Presheaf.IsLocallySurjective J f] : Function.S
urjective (Φ.presheafFiber.map f)
-/
lemma toPresheafFiber_map_bijective
    [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallySurjective J f] :
    Function.Bijective (Φ.presheafFiber.map f) :=
  ⟨Φ.toPresheafFiber_map_injective f, Φ.toPresheafFiber_map_surjective f⟩

/-- See also the lemma `W_isInvertedBy_presheafFiber` in the file
`Mathlib/CategoryTheory/Sites/Point/Basic.lean` which may apply
in more cases. -/
/-
**CategoryTheory.GrothendieckTopology.Point.W_isInvertedBy_presheafFiber'** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：W_isInvertedBy_presheafFiber' [J.WEqualsLocallyBijective A] [(forget A).Re
flectsIsomorphisms] : J.W.IsInvertedBy (Φ.presheafFiber (A
参数：forget A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.GrothendieckTopology.W_iff_isLocallyBijective`：W_iff_isLo
callyBijective : J.W f ↔ Presheaf.IsLocallyInjective J f ∧ Presheaf.IsLocallySur
jective J f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_map_bijective`
：toPresheafFiber_map_bijective [Presheaf.IsLocallyInjective J f] [Presheaf.IsLoc
allySurjective J f] : Function.Bijective (Φ.presheafFiber.map…

--- 原说明 ---
See also the lemma `W_isInvertedBy_presheafFiber` in the file
`Mathlib/CategoryTheory/Sites/Point/Basic.lean` which may apply
in more cases.
-/
lemma W_isInvertedBy_presheafFiber'
    [J.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms] :
    J.W.IsInvertedBy (Φ.presheafFiber (A := A)) := by
  intro P Q f hf
  obtain ⟨_, _⟩ := (J.W_iff_isLocallyBijective f).1 hf
  rw [← isIso_iff_of_reflects_iso _ (forget A), isIso_iff_bijective]
  exact Φ.toPresheafFiber_map_bijective f

end

/-- The fiber functor on the category of sheaves that is given a by a point of a site. -/
/-
**CategoryTheory.GrothendieckTopology.Point.sheafFiber** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：sheafFiber : Sheaf J A ⥤ A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber functor on the category of sheaves that is given a by a point of a sit
e.
-/
noncomputable def sheafFiber : Sheaf J A ⥤ A :=
  sheafToPresheaf J A ⋙ Φ.presheafFiber

/-- The fiber functor on sheaves is induced by the fiber functor on presheaves. -/
/-
**CategoryTheory.GrothendieckTopology.Point.sheafToPresheafCompPresheafFiberIso*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：sheafToPresheafCompPresheafFiberIso : sheafToPresheaf J A ⋙ Φ.presheafFibe
r ≅ Φ.sheafFiber
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber functor on sheaves is induced by the fiber functor on presheaves.
-/
noncomputable def sheafToPresheafCompPresheafFiberIso :
    sheafToPresheaf J A ⋙ Φ.presheafFiber ≅ Φ.sheafFiber :=
  Iso.refl _
/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallySmall.{w} C] [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
    PreservesFiniteLimits (Φ.presheafFiber (A := A)) :=
  comp_preservesFiniteLimits _ _
/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallySmall.{w} C] [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
    PreservesFiniteLimits (Φ.sheafFiber (A := A)) :=
  comp_preservesFiniteLimits _ _
/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesColimitsOfSize.{w, w} (Φ.presheafFiber (A := A)) where
  preservesColimitsOfShape := by
    dsimp [presheafFiber]
    infer_instance

section

variable [LocallySmall.{w} C]

/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesFiniteLimits Φ.fiber :=
  preservesFiniteLimits_of_natIso Φ.shrinkYonedaCompPresheafFiberIso

/-- The fiber of the terminal object is a terminal object in `Type w`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.isTerminalFiberObj** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：isTerminalFiberObj (T : C) (hT : IsTerminal T) : IsTerminal (Φ.fiber.obj T
)
参数：T : C；hT : IsTerminal T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber of the terminal object is a terminal object in `Type w`.
-/
noncomputable def isTerminalFiberObj (T : C) (hT : IsTerminal T) :
    IsTerminal (Φ.fiber.obj T) :=
  IsTerminal.isTerminalObj _ _ hT

/-- The fiber of the terminal object contains a unique element. -/
@[instance_reducible]
/-
**CategoryTheory.GrothendieckTopology.Point.uniqueFiberObj** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：uniqueFiberObj (T : C) (hT : IsTerminal T) : Unique (Φ.fiber.obj T)
参数：T : C；hT : IsTerminal T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber of the terminal object contains a unique element.
-/
noncomputable def uniqueFiberObj (T : C) (hT : IsTerminal T) :
    Unique (Φ.fiber.obj T) :=
  Types.isTerminalEquivUnique _ (Φ.isTerminalFiberObj T hT)
/-
**CategoryTheory.GrothendieckTopology.Point.fiber_map_injective_of_mono** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：fiber_map_injective_of_mono {U T : C} (f : U ⟶ T) [Mono f] : Function.Inje
ctive (Φ.fiber.map f)
参数：f : U ⟶ T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.mono_iff_injective`：mono_iff_injective {X Y : Type u} (f 
: X ⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instPreservesFiniteLimitsFiber
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.G
rothendieckTopology C} (Φ : J.Point)   [CategoryTheory.Locally…
-/
lemma fiber_map_injective_of_mono {U T : C} (f : U ⟶ T) [Mono f] :
    Function.Injective (Φ.fiber.map f) := by
  rw [← mono_iff_injective]
  infer_instance
/-
**CategoryTheory.GrothendieckTopology.Point.subsingleton_fiber_obj** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：subsingleton_fiber_obj {U T : C} (f : U ⟶ T) [Mono f] (hT : IsTerminal T) 
: Subsingleton (Φ.fiber.obj U) where allEq _ _
参数：f : U ⟶ T；hT : IsTerminal T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.fiber_map_injective_of_mono`：f
iber_map_injective_of_mono {U T : C} (f : U ⟶ T) [Mono f] : Function.Injective (
Φ.fiber.map f)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma subsingleton_fiber_obj {U T : C} (f : U ⟶ T) [Mono f] (hT : IsTerminal T) :
    Subsingleton (Φ.fiber.obj U) where
  allEq _ _ := Φ.fiber_map_injective_of_mono f (by
    have := Φ.uniqueFiberObj T hT
    subsingleton)

end

variable (F : A ⥤ B) [LocallySmall.{w} C] [PreservesFilteredColimitsOfSize.{w, w} F]

/-- If `Φ` is a point of a site and `F : A ⥤ B` is a functor which preserves
filtered colimits, then taking fibers of presheaves at `Φ` commutes with `F`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.presheafFiberCompIso** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：presheafFiberCompIso : (Functor.whiskeringRight _ _ _).obj F ⋙ Φ.presheafF
iber ≅ Φ.presheafFiber ⋙ F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instHasColimitsOfShapeOpposite
ElementsFiber`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Cat
egoryTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…

--- 原说明 ---
If `Φ` is a point of a site and `F : A ⥤ B` is a functor which preserves
filtered colimits, then taking fibers of presheaves at `Φ` commutes with `F`.
-/
noncomputable def presheafFiberCompIso :
    (Functor.whiskeringRight _ _ _).obj F ⋙ Φ.presheafFiber ≅
      Φ.presheafFiber ⋙ F :=
  haveI := Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{w} (Φ.fiber.Elementsᵒᵖ)) F
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft _ _ _).obj _) (preservesColimitNatIso F).symm

@[reassoc]
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_presheafFiberCompIso
_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiber_presheafFiberCompIso_hom_app (X : C) (x : Φ.fiber.obj X) (
P : Cᵒᵖ ⥤ A) : Φ.toPresheafFiber X x (P ⋙ F) ≫ (Φ.presheafFiberCompIso F).hom.ap
p P = F.map (Φ.toPresheafFiber X x P)
参数：X : C；x : Φ.fiber.obj X；P : Cᵒᵖ ⥤ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.preservesColimitsOfShape_of_final`：preserve
sColimitsOfShape_of_final {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B) [Preserves
ColimitsOfShape C H] : PreservesColimitsOfShape D H …
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.isCofiltered`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} (self : J.Point),   CategoryTheory.IsCo…
· 使用定理 `CategoryTheory.instLocallySmallOpposite`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C],   CategoryT
heory.LocallySmall.{w, v, u} …
· 使用定理 `CategoryTheory.CategoryOfElements.instLocallySmallElements`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v,
 u} C]   (F : CategoryTheory.Functor C (Type w))…
· 使用定理 `CategoryTheory.instFinallySmallOppositeOfInitiallySmall`：∀ {J : Type u} 
[inst : CategoryTheory.Category.{v, u} J] [CategoryTheory.InitiallySmall J],   C
ategoryTheory.FinallySmall Jᵒᵖ
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.initiallySmall`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopol
ogy C} (self : J.Point),   CategoryTheory.Init…
· 使用定理 `CategoryTheory.FinallySmall.instFinalFilteredFinalModelFromFilteredFinal
Model`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Catego
ryTheory.IsFiltered C]   [inst_2 : CategoryTheory.LocallySmall.{w, …
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.FinallySmall.instIsFilteredFilteredFinalModel`：∀ (C : Typ
e u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.IsFilter
ed C]   [inst_2 : CategoryTheory.LocallySmall.{w, …
· 使用定理 `CategoryTheory.ι_preservesColimitIso_inv`：ι_preservesColimitIso_inv (j :
 J) : colimit.ι _ j ≫ (preservesColimitIso G F).inv = G.map (colimit.ι F j)
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instHasColimitsOfShapeOpposite
ElementsFiber`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Cat
egoryTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
-/
lemma toPresheafFiber_presheafFiberCompIso_hom_app
    (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    Φ.toPresheafFiber X x (P ⋙ F) ≫ (Φ.presheafFiberCompIso F).hom.app P =
      F.map (Φ.toPresheafFiber X x P) := by
  have := Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{w} (Φ.fiber.Elementsᵒᵖ)) F
  simp only [presheafFiberCompIso]
  exact ι_preservesColimitIso_inv F ((CategoryOfElements.π Φ.fiber).op ⋙ P) _

/-- If `Φ` is a point of a site and `F : A ⥤ B` is a functor which preserves
filtered colimits, then taking fibers of sheaves at `Φ` commutes with `F`. -/
@[simps!]
/-
**CategoryTheory.GrothendieckTopology.Point.sheafFiberCompIso** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：sheafFiberCompIso [J.HasSheafCompose F] : sheafCompose J F ⋙ Φ.sheafFiber 
≅ Φ.sheafFiber ⋙ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Φ` is a point of a site and `F : A ⥤ B` is a functor which preserves
filtered colimits, then taking fibers of sheaves at `Φ` commutes with `F`.
-/
noncomputable def sheafFiberCompIso [J.HasSheafCompose F] :
    sheafCompose J F ⋙ Φ.sheafFiber ≅ Φ.sheafFiber ⋙ F :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (Φ.presheafFiberCompIso F) ≪≫
    (Functor.associator _ _ _).symm

end Point

end GrothendieckTopology

end CategoryTheory

