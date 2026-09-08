/-
Copyright (c) 2024 Alvaro Belmonte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvaro Belmonte, Joël Riou
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Data.ULift
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Codiscrete categories

We define `Codiscrete A` as an alias for the type `A`,
and use this type alias to provide a `Category` instance
whose Hom types are `Unit`.

`Codiscrete.functor` promotes a function `f : C → A` (for any category `C`) to a functor
`f : C ⥤ Codiscrete A`.

Similarly, `Codiscrete.natTrans` and `Codiscrete.natIso` promote `I`-indexed families of morphisms,
or `I`-indexed families of isomorphisms to natural transformations or natural isomorphisms.

We define `functorToCat : Type u ⥤ Cat.{0,u}` which sends a type to the codiscrete category and show
it is right adjoint to `Cat.objects`.
-/

@[expose] public section
namespace CategoryTheory

universe u v w

-- This is intentionally a structure rather than a type synonym
-- to enforce using `CodiscreteEquiv` (or `Codiscrete.mk` and `Codiscrete.as`) to move between
-- `Codiscrete α` and `α`. Otherwise there is too much API leakage.
/-- A wrapper for promoting any type to a category,
with a unique morphism between any two objects of the category.
-/
@[ext, aesop safe cases (rule_sets := [CategoryTheory])]
/-
**CategoryTheory.Codiscrete** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A wrapper for promoting any type to a category,
with a unique morphism between any two objects of the category.
-/
structure Codiscrete (α : Type u) where
  /-- A wrapper for promoting any type to a category,
  with a unique morphism between any two objects of the category. -/
  as : α

@[simp]
/-
**CategoryTheory.Codiscrete.mk_as** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Codi
screte`。
形式化陈述：∀ {α : Type u} (X : CategoryTheory.Codiscrete α), { as := X.as } = X
参数：X : CategoryTheory.Codiscrete α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Codiscrete.mk_as {α : Type u} (X : Codiscrete α) : Codiscrete.mk X.as = X := rfl

/-- `Codiscrete α` is equivalent to the original type `α`. -/
@[simps]
/-
**CategoryTheory.codiscreteEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：codiscreteEquiv {α : Type u} : Codiscrete α ≃ α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Codiscrete α` is equivalent to the original type `α`.
-/
def codiscreteEquiv {α : Type u} : Codiscrete α ≃ α where
  toFun := Codiscrete.as
  invFun := Codiscrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type u} [DecidableEq α] : DecidableEq (Codiscrete α) :=
  codiscreteEquiv.decidableEq

namespace Codiscrete

/-
**CategoryTheory.Codiscrete.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Codiscret
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : Type*) : Category (Codiscrete A) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

/-- Any two objects in a codiscrete category are isomorphic. -/
/-
**CategoryTheory.Codiscrete.iso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Codisc
rete`。
形式化陈述：iso {A : Type u} (x y : Codiscrete A) : x ≅ y where hom
参数：x y : Codiscrete A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any two objects in a codiscrete category are isomorphic.
-/
def iso {A : Type u} (x y : Codiscrete A) : x ≅ y where
  hom := ()
  inv := ()
/-
**CategoryTheory.Codiscrete.eq_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Codi
screte`。
形式化陈述：eq_id {A : Type u} {x : Codiscrete A} (f : x ⟶ x) : f = 𝟙 _
参数：f : x ⟶ x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eq_id {A : Type u} {x : Codiscrete A} (f : x ⟶ x) : f = 𝟙 _ := rfl
/-
**CategoryTheory.Codiscrete.eq_iso_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Codiscrete`。
形式化陈述：eq_iso_hom {A : Type u} {x y : Codiscrete A} (f : x ⟶ y) : f = (iso x y).h
om
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eq_iso_hom {A : Type u} {x y : Codiscrete A} (f : x ⟶ y) : f = (iso x y).hom := rfl
/-
**CategoryTheory.Codiscrete.eq_iso_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Codiscrete`。
形式化陈述：eq_iso_inv {A : Type u} {x y : Codiscrete A} (f : x ⟶ y) : f = (iso y x).i
nv
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eq_iso_inv {A : Type u} {x y : Codiscrete A} (f : x ⟶ y) : f = (iso y x).inv := rfl

@[simps]
/-
**CategoryTheory.Codiscrete.uniqueHom** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Codiscrete`。
形式化陈述：uniqueHom {A : Type u} (x y : Codiscrete A) : Unique (x ⟶ y) where default
参数：x y : Codiscrete A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueHom {A : Type u} (x y : Codiscrete A) : Unique (x ⟶ y) where
  default := (iso x y).hom
  uniq _ := rfl

@[simps]
/-
**CategoryTheory.Codiscrete.uniqueIso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Codiscrete`。
形式化陈述：uniqueIso {A : Type u} (x y : Codiscrete A) : Unique (x ≅ y) where default
参数：x y : Codiscrete A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueIso {A : Type u} (x y : Codiscrete A) : Unique (x ≅ y) where
  default := iso x y
  uniq _ := rfl

section
variable {C : Type u} [Category.{v} C] {A : Type w}

/-- Any function `C → A` lifts to a functor `C ⥤ Codiscrete A`. -/
/-
**CategoryTheory.Codiscrete.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Co
discrete`。
形式化陈述：functor (F : C -> A) : C ⥤ Codiscrete A where obj
参数：F : C -> A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any function `C → A` lifts to a functor `C ⥤ Codiscrete A`.
-/
def functor (F : C → A) : C ⥤ Codiscrete A where
  obj := Codiscrete.mk ∘ F
  map _ := ⟨⟩

/-- The underlying function `C → A` of a functor `C ⥤ Codiscrete A`. -/
/-
**CategoryTheory.Codiscrete.invFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Codiscrete`。
形式化陈述：invFunctor (F : C ⥤ Codiscrete A) : C -> A
参数：F : C ⥤ Codiscrete A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying function `C → A` of a functor `C ⥤ Codiscrete A`.
-/
def invFunctor (F : C ⥤ Codiscrete A) : C → A := Codiscrete.as ∘ F.obj

/-- Given two functors to a codiscrete category, there is a trivial natural transformation. -/
/-
**CategoryTheory.Codiscrete.natTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.C
odiscrete`。
形式化陈述：natTrans {F G : C ⥤ Codiscrete A} : F ⟶ G where app _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two functors to a codiscrete category, there is a trivial natural transfor
mation.
-/
def natTrans {F G : C ⥤ Codiscrete A} : F ⟶ G where
  app _ := ⟨⟩

/-- Given two functors into a codiscrete category, the trivial natural transformation is a
natural isomorphism. -/
/-
**CategoryTheory.Codiscrete.natIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cod
iscrete`。
形式化陈述：natIso {F G : C ⥤ Codiscrete A} : F ≅ G where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two functors into a codiscrete category, the trivial natural transformatio
n is a
natural isomorphism.
-/
def natIso {F G : C ⥤ Codiscrete A} : F ≅ G where
  hom := natTrans
  inv := natTrans

/-- Every functor `F` to a codiscrete category is naturally isomorphic (actually, equal) to
`Codiscrete.as ∘ F.obj`. -/
@[simps!]
/-
**CategoryTheory.Codiscrete.natIsoFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Codiscrete`。
形式化陈述：natIsoFunctor {F : C ⥤ Codiscrete A} : F ≅ functor (Codiscrete.as ∘ F.obj)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every functor `F` to a codiscrete category is naturally isomorphic (actually, eq
ual) to
`Codiscrete.as ∘ F.obj`.
-/
def natIsoFunctor {F : C ⥤ Codiscrete A} : F ≅ functor (Codiscrete.as ∘ F.obj) := Iso.refl _

end

/-- A function induces a functor between codiscrete categories. -/
/-
**CategoryTheory.Codiscrete.functorOfFun** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Codiscrete`。
形式化陈述：functorOfFun {A B : Type*} (f : A -> B) : Codiscrete A ⥤ Codiscrete B
参数：f : A -> B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function induces a functor between codiscrete categories.
-/
def functorOfFun {A B : Type*} (f : A → B) : Codiscrete A ⥤ Codiscrete B :=
  functor (f ∘ Codiscrete.as)

open Opposite

/-- A codiscrete category is equivalent to its opposite category. -/
/-
**CategoryTheory.Codiscrete.oppositeEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Codiscrete`。
形式化陈述：oppositeEquivalence (A : Type*) : (Codiscrete A)ᵒᵖ ≌ Codiscrete A where fu
nctor
参数：A : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A codiscrete category is equivalent to its opposite category.
-/
def oppositeEquivalence (A : Type*) : (Codiscrete A)ᵒᵖ ≌ Codiscrete A where
  functor := functor (fun x ↦ Codiscrete.as x.unop)
  inverse := (functor (fun x ↦ Codiscrete.as x.unop)).rightOp
  unitIso := NatIso.ofComponents (fun _ => by exact Iso.refl _)
  counitIso := natIso

/-- `Codiscrete.functorToCat` turns a type into a codiscrete category. -/
/-
**CategoryTheory.Codiscrete.functorToCat** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Codiscrete`。
形式化陈述：functorToCat : Type u ⥤ Cat.{0, u} where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Codiscrete.functorToCat` turns a type into a codiscrete category.
-/
def functorToCat : Type u ⥤ Cat.{0, u} where
  obj A := Cat.of (Codiscrete A)
  map f := (functorOfFun f).toCatHom

open Adjunction Cat

/-- For a category `C` and type `A`, there is an equivalence between functions `objects.obj C ⟶ A`
and functors `C ⥤ Codiscrete A`. -/
/-
**CategoryTheory.Codiscrete.equivFunctorToCodiscrete** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Codiscrete`。
形式化陈述：equivFunctorToCodiscrete {C : Type u} [Category.{v} C] {A : Type w} : (C -
> A) ≃ (C ⥤ Codiscrete A) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a category `C` and type `A`, there is an equivalence between functions `obje
cts.obj C ⟶ A`
and functors `C ⥤ Codiscrete A`.
-/
def equivFunctorToCodiscrete {C : Type u} [Category.{v} C] {A : Type w} :
    (C → A) ≃ (C ⥤ Codiscrete A) where
  toFun := functor
  invFun := invFunctor

/-- The functor that turns a type into a codiscrete category is right adjoint to the objects
functor. -/
/-
**CategoryTheory.Codiscrete.adj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Codisc
rete`。
形式化陈述：adj : objects ⊣ functorToCat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The functor that turns a type into a codiscrete category is right adjoint to the
 objects
functor.
-/
def adj : objects ⊣ functorToCat := mkOfHomEquiv {
  homEquiv _ _ := TypeCat.homEquiv.trans (equivFunctorToCodiscrete.trans (Functor.equivCatHom _ _))
  homEquiv_naturality_left_symm _ _ := rfl
  homEquiv_naturality_right _ _ := rfl }

/-- Components of the unit of the adjunction `Cat.objects ⊣ Codiscrete.functorToCat`. -/
/-
**CategoryTheory.Codiscrete.unitApp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Co
discrete`。
形式化陈述：unitApp (C : Type u) [Category.{v} C] : C ⥤ Codiscrete C
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Components of the unit of the adjunction `Cat.objects ⊣ Codiscrete.functorToCat`
.
-/
def unitApp (C : Type u) [Category.{v} C] : C ⥤ Codiscrete C := functor id

/-- Components of the counit of the adjunction `Cat.objects ⊣ Codiscrete.functorToCat` -/
/-
**CategoryTheory.Codiscrete.counitApp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Codiscrete`。
形式化陈述：counitApp (A : Type u) : Codiscrete A -> A
参数：A : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Components of the counit of the adjunction `Cat.objects ⊣ Codiscrete.functorToCa
t`
-/
def counitApp (A : Type u) : Codiscrete A → A := Codiscrete.as
/-
**CategoryTheory.Codiscrete.adj_unit_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Codiscrete`。
形式化陈述：adj_unit_app (X : Cat.{0, u}) : adj.unit.app X = (unitApp X).toCatHom
参数：X : Cat.{0, u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma adj_unit_app (X : Cat.{0, u}) :
    adj.unit.app X = (unitApp X).toCatHom := rfl
/-
**CategoryTheory.Codiscrete.adj_counit_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Codiscrete`。
形式化陈述：adj_counit_app (A : Type u) : adj.counit.app A = ↾(counitApp A)
参数：A : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma adj_counit_app (A : Type u) :
    adj.counit.app A = ↾(counitApp A) := rfl

/-- Left triangle equality of the adjunction `Cat.objects ⊣ Codiscrete.functorToCat`,
as a universe polymorphic statement. -/
/-
**CategoryTheory.Codiscrete.left_triangle_components** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Codiscrete`。
形式化陈述：left_triangle_components (C : Type u) [Category.{v} C] : (counitApp C).com
p (unitApp C).obj = id
参数：C : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left triangle equality of the adjunction `Cat.objects ⊣ Codiscrete.functorToCat`
,
as a universe polymorphic statement.
-/
lemma left_triangle_components (C : Type u) [Category.{v} C] :
    (counitApp C).comp (unitApp C).obj = id :=
  rfl

/-- Right triangle equality of the adjunction `Cat.objects ⊣ Codiscrete.functorToCat`,
stated using a composition of functors. -/
/-
**CategoryTheory.Codiscrete.right_triangle_components** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Codiscrete`。
形式化陈述：right_triangle_components (X : Type u) : unitApp (Codiscrete X) ⋙ functorO
fFun (counitApp X) = 𝟭 (Codiscrete X)
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right triangle equality of the adjunction `Cat.objects ⊣ Codiscrete.functorToCat
`,
stated using a composition of functors.
-/
lemma right_triangle_components (X : Type u) :
    unitApp (Codiscrete X) ⋙ functorOfFun (counitApp X) = 𝟭 (Codiscrete X) :=
  rfl

end Codiscrete

end CategoryTheory

