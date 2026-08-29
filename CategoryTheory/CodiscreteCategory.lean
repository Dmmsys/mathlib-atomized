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
/--
Definition of `Codiscrete` / `Codiscrete` 的定义

English:
structure Codiscrete
  parameters: (α : Type u)
  axioms and operations (1):
    - as : α

中文:
结构 余discrete
  参数: (α : 类型u)
  公理与运算 (1 个):
    - as : α
-/
structure Codiscrete (α : Type u) where
  /-- A wrapper for promoting any type to a category,
  with a unique morphism between any two objects of the category. -/
  as : α

@[simp]
/--
theorem `Codiscrete.mk_as` / 定理 `Codiscrete.mk_as`

English:
theorem Codiscrete.mk_as
  given: {α : Type u} (X : Codiscrete α)
  statement: Codiscrete.mk X.as = X
  proof: rfl

中文:
定理 余discrete.mk_as
  条件: {α : 类型u} (X : 余discrete α)
  结论: 余discrete.mk X.as = X
  证明: rfl
-/
theorem Codiscrete.mk_as {α : Type u} (X : Codiscrete α) : Codiscrete.mk X.as = X := rfl

/-- `Codiscrete α` is equivalent to the original type `α`. -/
@[simps]
/--
Definition of `codiscreteEquiv` / `codiscreteEquiv` 的定义

English:
definition codiscreteEquiv
  signature: {α : Type u}
  body: Codiscrete.as
  invFun := Codiscrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 codiscreteEquiv
  签名: {α : 类型u}
  定义体: Codiscrete.as
  invFun := Codiscrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: Codiscrete, Codiscrete.as
-/
def codiscreteEquiv {α : Type u} : Codiscrete α ≃ α where
  toFun := Codiscrete.as
  invFun := Codiscrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch

instance {α : Type u} [DecidableEq α] : DecidableEq (Codiscrete α) :=
  codiscreteEquiv.decidableEq

namespace Codiscrete

instance (A : Type*) : Category (Codiscrete A) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: {A : Type u} (x y : Codiscrete A)
  body: ()
  inv := ()

中文:
定义 iso
  签名: {A : 类型u} (x y : 余discrete A)
  定义体: ()
  inv := ()
-/
def iso {A : Type u} (x y : Codiscrete A) : x ≅ y where
  hom := ()
  inv := ()

/--
lemma `eq_id` / 引理 `eq_id`

English:
lemma eq_id
  given: {A : Type u} {x : Codiscrete A} (f : x ⟶ x)
  statement: f = 𝟙 _
  proof: rfl

中文:
引理 eq_id
  条件: {A : 类型u} {x : 余discrete A} (f : x ⟶ x)
  结论: f = 𝟙 _
  证明: rfl
-/
lemma eq_id {A : Type u} {x : Codiscrete A} (f : x ⟶ x) : f = 𝟙 _ := rfl

/--
lemma `eq_iso_hom` / 引理 `eq_iso_hom`

English:
lemma eq_iso_hom
  given: {A : Type u} {x y : Codiscrete A} (f : x ⟶ y)
  statement: f = (iso x y).hom
  proof: rfl

中文:
引理 eq_iso_hom
  条件: {A : 类型u} {x y : 余discrete A} (f : x ⟶ y)
  结论: f = (iso x y).hom
  证明: rfl
-/
lemma eq_iso_hom {A : Type u} {x y : Codiscrete A} (f : x ⟶ y) : f = (iso x y).hom := rfl

/--
lemma `eq_iso_inv` / 引理 `eq_iso_inv`

English:
lemma eq_iso_inv
  given: {A : Type u} {x y : Codiscrete A} (f : x ⟶ y)
  statement: f = (iso y x).inv
  proof: rfl

@[simps]

中文:
引理 eq_iso_inv
  条件: {A : 类型u} {x y : 余discrete A} (f : x ⟶ y)
  结论: f = (iso y x).inv
  证明: rfl

@[simps]
-/
lemma eq_iso_inv {A : Type u} {x y : Codiscrete A} (f : x ⟶ y) : f = (iso y x).inv := rfl

@[simps]
/--
Instance `uniqueHom` / 实例 `uniqueHom`

English:
instance uniqueHom
  signature: {A : Type u} (x y : Codiscrete A)
  body: (iso x y).hom
  uniq _ := rfl

@[simps]

中文:
实例 uniqueHom
  签名: {A : 类型u} (x y : 余discrete A)
  定义体: (iso x y).hom
  uniq _ := rfl

@[simps]
-/
instance uniqueHom {A : Type u} (x y : Codiscrete A) : Unique (x ⟶ y) where
  default := (iso x y).hom
  uniq _ := rfl

@[simps]
/--
Instance `uniqueIso` / 实例 `uniqueIso`

English:
instance uniqueIso
  signature: {A : Type u} (x y : Codiscrete A)
  body: iso x y
  uniq _ := rfl

中文:
实例 uniqueIso
  签名: {A : 类型u} (x y : 余discrete A)
  定义体: iso x y
  uniq _ := rfl
-/
instance uniqueIso {A : Type u} (x y : Codiscrete A) : Unique (x ≅ y) where
  default := iso x y
  uniq _ := rfl

section
variable {C : Type u} [Category.{v} C] {A : Type w}

/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: (F : C -> A)
  body: Codiscrete.mk ∘ F
  map _ := ⟨⟩

中文:
定义 functor
  签名: (F : C -> A)
  定义体: Codiscrete.mk ∘ F
  map _ := ⟨⟩

Depends on / 依赖: Codiscrete, Codiscrete.mk
-/
def functor (F : C -> A) : C ⥤ Codiscrete A where
  obj := Codiscrete.mk ∘ F
  map _ := ⟨⟩

/--
Definition of `invFunctor` / `invFunctor` 的定义

English:
definition invFunctor
  signature: (F : C ⥤ Codiscrete A)
  body: Codiscrete.as ∘ F.obj

中文:
定义 invFunctor
  签名: (F : C ⥤ 余discrete A)
  定义体: Codiscrete.as ∘ F.obj

Depends on / 依赖: Codiscrete, Codiscrete.as, F.obj
-/
def invFunctor (F : C ⥤ Codiscrete A) : C -> A := Codiscrete.as ∘ F.obj

/--
Definition of `natTrans` / `natTrans` 的定义

English:
definition natTrans
  signature: {F G : C ⥤ Codiscrete A}
  body: ⟨⟩

中文:
定义 natTrans
  签名: {F G : C ⥤ 余discrete A}
  定义体: ⟨⟩
-/
def natTrans {F G : C ⥤ Codiscrete A} : F ⟶ G where
  app _ := ⟨⟩

/--
Definition of `natIso` / `natIso` 的定义

English:
definition natIso
  signature: {F G : C ⥤ Codiscrete A}
  body: natTrans
  inv := natTrans

中文:
定义 natIso
  签名: {F G : C ⥤ 余discrete A}
  定义体: natTrans
  inv := natTrans

Depends on / 依赖: natTrans
-/
def natIso {F G : C ⥤ Codiscrete A} : F ≅ G where
  hom := natTrans
  inv := natTrans

/-- Every functor `F` to a codiscrete category is naturally isomorphic (actually, equal) to
`Codiscrete.as ∘ F.obj`. -/
@[simps!]
/--
Definition of `natIsoFunctor` / `natIsoFunctor` 的定义

English:
definition natIsoFunctor
  signature: {F : C ⥤ Codiscrete A}
  body: Iso.refl _

中文:
定义 natIsoFunctor
  签名: {F : C ⥤ 余discrete A}
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def natIsoFunctor {F : C ⥤ Codiscrete A} : F ≅ functor (Codiscrete.as ∘ F.obj) := Iso.refl _

end

/--
Definition of `functorOfFun` / `functorOfFun` 的定义

English:
definition functorOfFun
  signature: {A B : Type*} (f : A -> B)
  body: functor (f ∘ Codiscrete.as)

中文:
定义 functorOfFun
  签名: {A B : 类型} (f : A -> B)
  定义体: functor (f ∘ Codiscrete.as)

Depends on / 依赖: Codiscrete, Codiscrete.as, functor
-/
def functorOfFun {A B : Type*} (f : A -> B) : Codiscrete A ⥤ Codiscrete B :=
  functor (f ∘ Codiscrete.as)

open Opposite

/--
Definition of `oppositeEquivalence` / `oppositeEquivalence` 的定义

English:
definition oppositeEquivalence
  signature: (A : Type*)
  body: functor (fun x => Codiscrete.as x.unop)
  inverse := (functor (fun x => Codiscrete.as x.unop)).rightOp
  unitIso := NatIso.ofComponents (fun _ => by exact Iso.refl _)
  counitIso := natIso

中文:
定义 oppositeEquivalence
  签名: (A : 类型)
  定义体: functor (fun x => Codiscrete.as x.unop)
  inverse := (functor (fun x => Codiscrete.as x.unop)).rightOp
  unitIso := NatIso.ofComponents (fun _ => by exact Iso.refl _)
  counitIso := natIso

Depends on / 依赖: Codiscrete, Codiscrete.as, functor, x.unop
-/
def oppositeEquivalence (A : Type*) : (Codiscrete A)ᵒᵖ ≌ Codiscrete A where
  functor := functor (fun x => Codiscrete.as x.unop)
  inverse := (functor (fun x => Codiscrete.as x.unop)).rightOp
  unitIso := NatIso.ofComponents (fun _ => by exact Iso.refl _)
  counitIso := natIso

/--
Definition of `functorToCat` / `functorToCat` 的定义

English:
definition functorToCat
  signature: : Type u ⥤ Cat.{0, u} where
  body: Cat.of (Codiscrete A)
  map f := (functorOfFun f).toCatHom

中文:
定义 functorToCat
  签名: : 类型u ⥤ Cat.{0, u} where
  定义体: Cat.of (Codiscrete A)
  map f := (functorOfFun f).toCatHom

Depends on / 依赖: Cat.of, Codiscrete
-/
def functorToCat : Type u ⥤ Cat.{0, u} where
  obj A := Cat.of (Codiscrete A)
  map f := (functorOfFun f).toCatHom

open Adjunction Cat

/--
Definition of `equivFunctorToCodiscrete` / `equivFunctorToCodiscrete` 的定义

English:
definition equivFunctorToCodiscrete
  signature: {C : Type u} [Category.{v} C] {A : Type w}
  body: functor
  invFun := invFunctor

中文:
定义 equivFunctorToCodiscrete
  签名: {C : 类型u} [范畴.{v} C] {A : 类型 w}
  定义体: functor
  invFun := invFunctor

Depends on / 依赖: functor
-/
def equivFunctorToCodiscrete {C : Type u} [Category.{v} C] {A : Type w} :
    (C -> A) ≃ (C ⥤ Codiscrete A) where
  toFun := functor
  invFun := invFunctor

/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : objects ⊣ functorToCat
  body: mkOfHomEquiv {
  homEquiv _ _ := TypeCat.homEquiv.trans (equivFunctorToCodiscrete.trans (Functor.equivCatHom _ _))
  homEquiv_naturality_left_symm _ _ := rfl
  homEquiv_naturality_right _ _ := rfl }

中文:
定义 adj
  签名: : objects ⊣ functorToCat
  定义体: mkOfHomEquiv {
  homEquiv _ _ := TypeCat.homEquiv.trans (equivFunctorToCodiscrete.trans (Functor.equivCatHom _ _))
  homEquiv_naturality_left_symm _ _ := rfl
  homEquiv_naturality_right _ _ := rfl }

Depends on / 依赖: mkOfHomEquiv
-/
def adj : objects ⊣ functorToCat := mkOfHomEquiv {
  homEquiv _ _ := TypeCat.homEquiv.trans (equivFunctorToCodiscrete.trans (Functor.equivCatHom _ _))
  homEquiv_naturality_left_symm _ _ := rfl
  homEquiv_naturality_right _ _ := rfl }

/--
Definition of `unitApp` / `unitApp` 的定义

English:
definition unitApp
  signature: (C : Type u) [Category.{v} C]
  body: functor id

中文:
定义 unitApp
  签名: (C : 类型u) [范畴.{v} C]
  定义体: functor id

Depends on / 依赖: functor
-/
def unitApp (C : Type u) [Category.{v} C] : C ⥤ Codiscrete C := functor id

/--
Definition of `counitApp` / `counitApp` 的定义

English:
definition counitApp
  signature: (A : Type u)
  body: Codiscrete.as

中文:
定义 counitApp
  签名: (A : 类型u)
  定义体: Codiscrete.as

Depends on / 依赖: Codiscrete, Codiscrete.as
-/
def counitApp (A : Type u) : Codiscrete A -> A := Codiscrete.as

/--
lemma `adj_unit_app` / 引理 `adj_unit_app`

English:
lemma adj_unit_app
  given: (X : Cat.{0, u})
  proof: rfl

中文:
引理 adj_unit_app
  条件: (X : Cat.{0, u})
  证明: rfl
-/
lemma adj_unit_app (X : Cat.{0, u}) :
    adj.unit.app X = (unitApp X).toCatHom := rfl

/--
lemma `adj_counit_app` / 引理 `adj_counit_app`

English:
lemma adj_counit_app
  given: (A : Type u)
  proof: rfl

中文:
引理 adj_counit_app
  条件: (A : 类型u)
  证明: rfl
-/
lemma adj_counit_app (A : Type u) :
    adj.counit.app A = ↾(counitApp A) := rfl

/--
lemma `left_triangle_components` / 引理 `left_triangle_components`

English:
lemma left_triangle_components
  given: (C : Type u) [Category.{v} C]
  proof: rfl

中文:
引理 left_triangle_components
  条件: (C : 类型u) [范畴.{v} C]
  证明: rfl
-/
lemma left_triangle_components (C : Type u) [Category.{v} C] :
    (counitApp C).comp (unitApp C).obj = id :=
  rfl

/--
lemma `right_triangle_components` / 引理 `right_triangle_components`

English:
lemma right_triangle_components
  given: (X : Type u)
  proof: rfl

中文:
引理 right_triangle_components
  条件: (X : 类型u)
  证明: rfl
-/
lemma right_triangle_components (X : Type u) :
    unitApp (Codiscrete X) ⋙ functorOfFun (counitApp X) = 𝟭 (Codiscrete X) :=
  rfl

end Codiscrete

end CategoryTheory
