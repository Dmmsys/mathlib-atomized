/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Eilenberg-Moore (co)algebras for a (co)monad

This file defines Eilenberg-Moore (co)algebras for a (co)monad,
and provides the category instance for them.

Further it defines the adjoint pair of free and forgetful functors, respectively
from and to the original category, as well as the adjoint pair of forgetful and
cofree functors, respectively from and to the original category.

## References
* [Riehl, *Category theory in context*, Section 5.2.4][riehl2017]
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


namespace CategoryTheory

open Category

universe v₁ u₁

-- morphism levels before object levels. See note [category_theory universes].
variable {C : Type u₁} [Category.{v₁} C]

namespace Monad

/--
Definition of `Algebra` / `Algebra` 的定义

English:
structure Algebra
  parameters: (T : Monad C)
  axioms and operations (4):
    - A : C
    - a : (T : C ⥤ C).obj A ⟶ A
    - unit : T.η.app A ≫ a = 𝟙 A  [default: by cat_disch]
    - assoc : T.μ.app A ≫ a = (T : C ⥤ C).map a ≫ a  [default: by cat_disch]

中文:
结构 Algebra
  参数: (T : Monad C)
  公理与运算 (4 个):
    - A : C
    - a : (T : C ⥤ C).obj A ⟶ A
    - unit : T.η.app A ≫ a = 𝟙 A  [默认: by cat_disch]
    - assoc : T.μ.app A ≫ a = (T : C ⥤ C).map a ≫ a  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Algebra (T : Monad C) : Type max u₁ v₁ where
  /-- The underlying object associated to an algebra. -/
  A : C
  /-- The structure morphism associated to an algebra. -/
  a : (T : C ⥤ C).obj A ⟶ A
  /-- The unit axiom associated to an algebra. -/
  unit : T.η.app A ≫ a = 𝟙 A := by cat_disch
  /-- The associativity axiom associated to an algebra. -/
  assoc : T.μ.app A ≫ a = (T : C ⥤ C).map a ≫ a := by cat_disch

attribute [reassoc] Algebra.unit Algebra.assoc

namespace Algebra

variable {T : Monad C}

/-- A morphism of Eilenberg–Moore algebras for the monad `T`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (A B : Algebra T)
  axioms and operations (2):
    - f : A.A ⟶ B.A
    - h : (T : C ⥤ C).map f ≫ B.a = A.a ≫ f  [default: by cat_disch]

中文:
结构 Hom
  参数: (A B : Algebra T)
  公理与运算 (2 个):
    - f : A.A ⟶ B.A
    - h : (T : C ⥤ C).map f ≫ B.a = A.a ≫ f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (A B : Algebra T) where
  /-- The underlying morphism associated to a morphism of algebras. -/
  f : A.A ⟶ B.A
  /-- Compatibility with the structure morphism, for a morphism of algebras. -/
  h : (T : C ⥤ C).map f ≫ B.a = A.a ≫ f := by cat_disch

attribute [reassoc (attr := simp)] Hom.h

namespace Hom

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (A : Algebra T)
  body: 𝟙 A.A

中文:
定义 id
  签名: (A : Algebra T)
  定义体: 𝟙 A.A
-/
def id (A : Algebra T) : Hom A A where f := 𝟙 A.A

instance (A : Algebra T) : Inhabited (Hom A A) :=
  ⟨{ f := 𝟙 _ }⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {P Q R : Algebra T} (f : Hom P Q) (g : Hom Q R)
  body: f.f ≫ g.f

中文:
定义 comp
  签名: {P Q R : Algebra T} (f : Hom P Q) (g : Hom Q R)
  定义体: f.f ≫ g.f
-/
def comp {P Q R : Algebra T} (f : Hom P Q) (g : Hom Q R) : Hom P R where f := f.f ≫ g.f

end Hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryStruct (Algebra T)
  body: Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]

中文:
实例 :
  签名: CategoryStruct (Algebra T)
  定义体: Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
-/
instance : CategoryStruct (Algebra T) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
/--
lemma `Hom.ext'` / 引理 `Hom.ext'`

English:
lemma Hom.ext'
  given: (X Y : Algebra T) (f g : X ⟶ Y) (h : f.f = g.f)
  statement: f = g
  proof: Hom.ext h

@[simp]

中文:
引理 Hom.ext'
  条件: (X Y : Algebra T) (f g : X ⟶ Y) (h : f.f = g.f)
  结论: f = g
  证明: Hom.ext h

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma Hom.ext' (X Y : Algebra T) (f g : X ⟶ Y) (h : f.f = g.f) : f = g := Hom.ext h

@[simp]
/--
theorem `comp_eq_comp` / 定理 `comp_eq_comp`

English:
theorem comp_eq_comp
  given: {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'')
  proof: rfl

@[simp]

中文:
定理 comp_eq_comp
  条件: {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'')
  证明: rfl

@[simp]
-/
theorem comp_eq_comp {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'') :
    Algebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
/--
theorem `id_eq_id` / 定理 `id_eq_id`

English:
theorem id_eq_id
  given: (A : Algebra T)
  statement: Algebra.Hom.id A = 𝟙 A
  proof: rfl

@[simp]

中文:
定理 id_eq_id
  条件: (A : Algebra T)
  结论: Algebra.Hom.id A = 𝟙 A
  证明: rfl

@[simp]
-/
theorem id_eq_id (A : Algebra T) : Algebra.Hom.id A = 𝟙 A :=
  rfl

@[simp]
/--
theorem `id_f` / 定理 `id_f`

English:
theorem id_f
  given: (A : Algebra T)
  statement: (𝟙 A : A ⟶ A).f = 𝟙 A.A
  proof: rfl

@[simp]

中文:
定理 id_f
  条件: (A : Algebra T)
  结论: (𝟙 A : A ⟶ A).f = 𝟙 A.A
  证明: rfl

@[simp]
-/
theorem id_f (A : Algebra T) : (𝟙 A : A ⟶ A).f = 𝟙 A.A :=
  rfl

@[simp]
/--
theorem `comp_f` / 定理 `comp_f`

English:
theorem comp_f
  given: {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'')
  statement: (f ≫ g).f = f.f ≫ g.f
  proof: rfl

中文:
定理 comp_f
  条件: {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'')
  结论: (f ≫ g).f = f.f ≫ g.f
  证明: rfl
-/
theorem comp_f {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'') : (f ≫ g).f = f.f ≫ g.f :=
  rfl

/--
Instance `eilenbergMoore` / 实例 `eilenbergMoore`

English:
instance eilenbergMoore
  signature: : Category (Algebra T) where

中文:
实例 eilenbergMoore
  签名: : Category (Algebra T) where
-/
instance eilenbergMoore : Category (Algebra T) where

/--
To construct an isomorphism of algebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {A B : Algebra T} (h : A.A ≅ B.A)
  body: { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_comp_inv]; rw [Category.assoc]; rw [← w]; rw [← Functor.map_comp_assoc]
        simp }

中文:
定义 isoMk
  签名: {A B : Algebra T} (h : A.A ≅ B.A)
  定义体: { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_comp_inv]; rw [Category.assoc]; rw [← w]; rw [← Functor.map_comp_assoc]
        simp }

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp_assoc, cat_disch, eq_comp_inv, h.eq_comp_inv, h.hom, h.inv, map_comp_assoc
-/
def isoMk {A B : Algebra T} (h : A.A ≅ B.A)
    (w : (T : C ⥤ C).map h.hom ≫ B.a = A.a ≫ h.hom := by cat_disch) : A ≅ B where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_comp_inv]; rw [Category.assoc]; rw [← w]; rw [← Functor.map_comp_assoc]
        simp }

end Algebra

variable (T : Monad C)

/-- The forgetful functor from the Eilenberg-Moore category, forgetting the algebraic structure. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Algebra T ⥤ C where
  body: A.A
  map f := f.f

中文:
定义 forget
  签名: : Algebra T ⥤ C where
  定义体: A.A
  map f := f.f
-/
def forget : Algebra T ⥤ C where
  obj A := A.A
  map f := f.f

/-- The free functor from the Eilenberg-Moore category, constructing an algebra for any object. -/
@[simps]
/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: : C ⥤ Algebra T where
  body: { A := T.obj X
      a := T.μ.app X
      assoc := (T.assoc _).symm }
  map f :=
    { f := T.map f
      h := T.μ.naturality _ }

中文:
定义 free
  签名: : C ⥤ Algebra T where
  定义体: { A := T.obj X
      a := T.μ.app X
      assoc := (T.assoc _).symm }
  map f :=
    { f := T.map f
      h := T.μ.naturality _ }

Depends on / 依赖: T.assoc, T.map, T.obj, naturality
-/
def free : C ⥤ Algebra T where
  obj X :=
    { A := T.obj X
      a := T.μ.app X
      assoc := (T.assoc _).symm }
  map f :=
    { f := T.map f
      h := T.μ.naturality _ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: C] : Inhabited (Algebra T)
  body: ⟨(free T).obj default⟩

中文:
实例 [Inhabited
  签名: C] : Inhabited (Algebra T)
  定义体: ⟨(free T).obj default⟩
-/
instance [Inhabited C] : Inhabited (Algebra T) :=
  ⟨(free T).obj default⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- The other two `simps` projection lemmas can be derived from these two, so `simp_nf` complains if
-- those are added too
/-- The adjunction between the free and forgetful constructions for Eilenberg-Moore algebras for
  a monad. cf Lemma 5.2.8 of [Riehl][riehl2017]. -/
@[simps! unit counit]
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : T.free ⊣ T.forget
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => T.η.app X ≫ f.f
          invFun := fun f =>
            { f := T.map f ≫ Y.a
              h := by simp [← Y.assoc, ← T.μ.naturality_assoc] }
          left_inv := fun f => by
            ext
            simp
         

中文:
定义 adj
  签名: : T.free ⊣ T.forget
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => T.η.app X ≫ f.f
          invFun := fun f =>
            { f := T.map f ≫ Y.a
              h := by simp [← Y.assoc, ← T.μ.naturality_assoc] }
          left_inv := fun f => by
            ext
            simp
         

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Category, Category.comp_id, T.map, Y.assoc, Y.unit, comp_id, forget_obj, homEquiv, invFun, left_inv, mkOfHomEquiv, naturality_assoc, right_inv
-/
def adj : T.free ⊣ T.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => T.η.app X ≫ f.f
          invFun := fun f =>
            { f := T.map f ≫ Y.a
              h := by simp [← Y.assoc, ← T.μ.naturality_assoc] }
          left_inv := fun f => by
            ext
            simp
          right_inv := fun f => by
            dsimp only [forget_obj]
            rw [← T.η.naturality_assoc]; rw [Y.unit]
            apply Category.comp_id } }

/--
theorem `algebra_iso_of_iso` / 定理 `algebra_iso_of_iso`

English:
theorem algebra_iso_of_iso
  given: {A B : Algebra T} (f : A ⟶ B) [IsIso f.f]
  statement: IsIso f
  proof: ⟨⟨{ f := inv f.f, h := by simp }, by cat_disch⟩⟩

中文:
定理 algebra_iso_of_iso
  条件: {A B : Algebra T} (f : A ⟶ B) [IsIso f.f]
  结论: IsIso f
  证明: ⟨⟨{ f := inv f.f, h := by simp }, by cat_disch⟩⟩

Depends on / 依赖: cat_disch
-/
theorem algebra_iso_of_iso {A B : Algebra T} (f : A ⟶ B) [IsIso f.f] : IsIso f :=
  ⟨⟨{ f := inv f.f, h := by simp }, by cat_disch⟩⟩

/--
Instance `forget_reflects_iso` / 实例 `forget_reflects_iso`

English:
instance forget_reflects_iso
  signature: : T.forget.ReflectsIsomorphisms where
  body: algebra_iso_of_iso T f

中文:
实例 forget_reflects_iso
  签名: : T.forget.ReflectsIsomorphisms where
  定义体: algebra_iso_of_iso T f

Depends on / 依赖: algebra_iso_of_iso
-/
instance forget_reflects_iso : T.forget.ReflectsIsomorphisms where
  reflects {_ _} f [IsIso f.f] := algebra_iso_of_iso T f

/--
Instance `forget_faithful` / 实例 `forget_faithful`

English:
instance forget_faithful
  signature: : T.forget.Faithful where

中文:
实例 forget_faithful
  签名: : T.forget.Faithful where
-/
instance forget_faithful : T.forget.Faithful where

/--
theorem `algebra_epi_of_epi` / 定理 `algebra_epi_of_epi`

English:
theorem algebra_epi_of_epi
  given: {X Y : Algebra T} (f : X ⟶ Y) [h : Epi f.f]
  statement: Epi f
  proof: (forget T).epi_of_epi_map h

中文:
定理 algebra_epi_of_epi
  条件: {X Y : Algebra T} (f : X ⟶ Y) [h : Epi f.f]
  结论: Epi f
  证明: (forget T).epi_of_epi_map h

Depends on / 依赖: epi_of_epi_map, forget
-/
theorem algebra_epi_of_epi {X Y : Algebra T} (f : X ⟶ Y) [h : Epi f.f] : Epi f :=
  (forget T).epi_of_epi_map h

/--
theorem `algebra_mono_of_mono` / 定理 `algebra_mono_of_mono`

English:
theorem algebra_mono_of_mono
  given: {X Y : Algebra T} (f : X ⟶ Y) [h : Mono f.f]
  statement: Mono f
  proof: (forget T).mono_of_mono_map h

中文:
定理 algebra_mono_of_mono
  条件: {X Y : Algebra T} (f : X ⟶ Y) [h : Mono f.f]
  结论: Mono f
  证明: (forget T).mono_of_mono_map h

Depends on / 依赖: forget, mono_of_mono_map
-/
theorem algebra_mono_of_mono {X Y : Algebra T} (f : X ⟶ Y) [h : Mono f.f] : Mono f :=
  (forget T).mono_of_mono_map h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T.forget.IsRightAdjoint
  body: ⟨T.free, ⟨T.adj⟩⟩

中文:
实例 :
  签名: T.forget.IsRightAdjoint
  定义体: ⟨T.free, ⟨T.adj⟩⟩

Depends on / 依赖: T.adj, T.free
-/
instance : T.forget.IsRightAdjoint :=
  ⟨T.free, ⟨T.adj⟩⟩

/--
Given a monad morphism from `T₂` to `T₁`, we get a functor from the algebras of `T₁` to algebras of
`T₂`.
-/
@[simps]
/--
Definition of `algebraFunctorOfMonadHom` / `algebraFunctorOfMonadHom` 的定义

English:
definition algebraFunctorOfMonadHom
  signature: {T₁ T₂ : Monad C} (h : T₂ ⟶ T₁)
  body: { A := A.A
      a := h.app A.A ≫ A.a
      unit := by simp [A.unit]
      assoc := by simp [A.assoc] }
  map f := { f := f.f }

中文:
定义 algebraFunctorOfMonadHom
  签名: {T₁ T₂ : Monad C} (h : T₂ ⟶ T₁)
  定义体: { A := A.A
      a := h.app A.A ≫ A.a
      unit := by simp [A.unit]
      assoc := by simp [A.assoc] }
  map f := { f := f.f }

Depends on / 依赖: A.assoc, A.unit, h.app
-/
def algebraFunctorOfMonadHom {T₁ T₂ : Monad C} (h : T₂ ⟶ T₁) : Algebra T₁ ⥤ Algebra T₂ where
  obj A :=
    { A := A.A
      a := h.app A.A ≫ A.a
      unit := by simp [A.unit]
      assoc := by simp [A.assoc] }
  map f := { f := f.f }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
The identity monad morphism induces the identity functor from the category of algebras to itself.
-/
@[simps (rhsMd := .default)]
/--
Definition of `algebraFunctorOfMonadHomId` / `algebraFunctorOfMonadHomId` 的定义

English:
definition algebraFunctorOfMonadHomId
  signature: {T₁ : Monad C}
  body: NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

中文:
定义 algebraFunctorOfMonadHomId
  签名: {T₁ : Monad C}
  定义体: NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

Depends on / 依赖: Algebra, Algebra.isoMk, Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def algebraFunctorOfMonadHomId {T₁ : Monad C} : algebraFunctorOfMonadHom (𝟙 T₁) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A composition of monad morphisms gives the composition of corresponding functors.
-/
@[simps (rhsMd := .default)]
/--
Definition of `algebraFunctorOfMonadHomComp` / `algebraFunctorOfMonadHomComp` 的定义

English:
definition algebraFunctorOfMonadHomComp
  signature: {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)
  body: NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

中文:
定义 algebraFunctorOfMonadHomComp
  签名: {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)
  定义体: NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

Depends on / 依赖: Algebra, Algebra.isoMk, Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def algebraFunctorOfMonadHomComp {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    algebraFunctorOfMonadHom (f ≫ g) ≅ algebraFunctorOfMonadHom g ⋙ algebraFunctorOfMonadHom f :=
  NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f` and `g` are two equal morphisms of monads, then the functors of algebras induced by them
are isomorphic.
We define it like this as opposed to using `eqToIso` so that the components are nicer to prove
lemmas about.
-/
@[simps (rhsMd := .default)]
/--
Definition of `algebraFunctorOfMonadHomEq` / `algebraFunctorOfMonadHomEq` 的定义

English:
definition algebraFunctorOfMonadHomEq
  signature: {T₁ T₂ : Monad C} {f g : T₁ ⟶ T₂} (h : f = g)
  body: NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

中文:
定义 algebraFunctorOfMonadHomEq
  签名: {T₁ T₂ : Monad C} {f g : T₁ ⟶ T₂} (h : f = g)
  定义体: NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

Depends on / 依赖: Algebra, Algebra.isoMk, Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def algebraFunctorOfMonadHomEq {T₁ T₂ : Monad C} {f g : T₁ ⟶ T₂} (h : f = g) :
    algebraFunctorOfMonadHom f ≅ algebraFunctorOfMonadHom g :=
  NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Isomorphic monads give equivalent categories of algebras. Furthermore, they are equivalent as
categories over `C`, that is, we have `algebraEquivOfIsoMonads h ⋙ forget = forget`.
-/
@[simps]
/--
Definition of `algebraEquivOfIsoMonads` / `algebraEquivOfIsoMonads` 的定义

English:
definition algebraEquivOfIsoMonads
  signature: {T₁ T₂ : Monad C} (h : T₁ ≅ T₂)
  body: algebraFunctorOfMonadHom h.inv
  inverse := algebraFunctorOfMonadHom h.hom
  unitIso :=
    algebraFunctorOfMonadHomId.symm ≪≫
      algebraFunctorOfMonadHomEq (by simp) ≪≫ algebraFunctorOfMonadHomComp _ _
  counitIso :=
    (algebraFunctorOfMonadHomComp _ _).symm ≪≫
      algebraFunctorOfMonadHomEq

中文:
定义 algebraEquivOfIsoMonads
  签名: {T₁ T₂ : Monad C} (h : T₁ ≅ T₂)
  定义体: algebraFunctorOfMonadHom h.inv
  inverse := algebraFunctorOfMonadHom h.hom
  unitIso :=
    algebraFunctorOfMonadHomId.symm ≪≫
      algebraFunctorOfMonadHomEq (by simp) ≪≫ algebraFunctorOfMonadHomComp _ _
  counitIso :=
    (algebraFunctorOfMonadHomComp _ _).symm ≪≫
      algebraFunctorOfMonadHomEq

Depends on / 依赖: algebraFunctorOfMonadHom, h.inv
-/
def algebraEquivOfIsoMonads {T₁ T₂ : Monad C} (h : T₁ ≅ T₂) : Algebra T₁ ≌ Algebra T₂ where
  functor := algebraFunctorOfMonadHom h.inv
  inverse := algebraFunctorOfMonadHom h.hom
  unitIso :=
    algebraFunctorOfMonadHomId.symm ≪≫
      algebraFunctorOfMonadHomEq (by simp) ≪≫ algebraFunctorOfMonadHomComp _ _
  counitIso :=
    (algebraFunctorOfMonadHomComp _ _).symm ≪≫
      algebraFunctorOfMonadHomEq (by simp) ≪≫ algebraFunctorOfMonadHomId

@[simp]
/--
theorem `algebra_equiv_of_iso_monads_comp_forget` / 定理 `algebra_equiv_of_iso_monads_comp_forget`

English:
theorem algebra_equiv_of_iso_monads_comp_forget
  given: {T₁ T₂ : Monad C} (h : T₁ ⟶ T₂)
  proof: rfl

中文:
定理 algebra_equiv_of_iso_monads_comp_forget
  条件: {T₁ T₂ : Monad C} (h : T₁ ⟶ T₂)
  证明: rfl
-/
theorem algebra_equiv_of_iso_monads_comp_forget {T₁ T₂ : Monad C} (h : T₁ ⟶ T₂) :
    algebraFunctorOfMonadHom h ⋙ forget _ = forget _ :=
  rfl

end Monad

namespace Comonad

/--
Definition of `Coalgebra` / `Coalgebra` 的定义

English:
structure Coalgebra
  parameters: (G : Comonad C)
  axioms and operations (4):
    - A : C
    - a : A ⟶ (G : C ⥤ C).obj A
    - counit : a ≫ G.ε.app A = 𝟙 A  [default: by cat_disch]
    - coassoc : a ≫ G.δ.app A = a ≫ G.map a  [default: by cat_disch]

中文:
结构 Coalgebra
  参数: (G : Comonad C)
  公理与运算 (4 个):
    - A : C
    - a : A ⟶ (G : C ⥤ C).obj A
    - counit : a ≫ G.ε.app A = 𝟙 A  [默认: by cat_disch]
    - coassoc : a ≫ G.δ.app A = a ≫ G.map a  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Coalgebra (G : Comonad C) : Type max u₁ v₁ where
  /-- The underlying object associated to a coalgebra. -/
  A : C
  /-- The structure morphism associated to a coalgebra. -/
  a : A ⟶ (G : C ⥤ C).obj A
  /-- The counit axiom associated to a coalgebra. -/
  counit : a ≫ G.ε.app A = 𝟙 A := by cat_disch
  /-- The coassociativity axiom associated to a coalgebra. -/
  coassoc : a ≫ G.δ.app A = a ≫ G.map a := by cat_disch


attribute [reassoc] Coalgebra.counit Coalgebra.coassoc

namespace Coalgebra

variable {G : Comonad C}

/-- A morphism of Eilenberg-Moore coalgebras for the comonad `G`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (A B : Coalgebra G)
  axioms and operations (2):
    - f : A.A ⟶ B.A
    - h : A.a ≫ (G : C ⥤ C).map f = f ≫ B.a  [default: by cat_disch]

中文:
结构 Hom
  参数: (A B : Coalgebra G)
  公理与运算 (2 个):
    - f : A.A ⟶ B.A
    - h : A.a ≫ (G : C ⥤ C).map f = f ≫ B.a  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (A B : Coalgebra G) where
  /-- The underlying morphism associated to a morphism of coalgebras. -/
  f : A.A ⟶ B.A
  /-- Compatibility with the structure morphism, for a morphism of coalgebras. -/
  h : A.a ≫ (G : C ⥤ C).map f = f ≫ B.a := by cat_disch

attribute [reassoc (attr := simp)] Hom.h

namespace Hom

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (A : Coalgebra G)
  body: 𝟙 A.A

中文:
定义 id
  签名: (A : Coalgebra G)
  定义体: 𝟙 A.A
-/
def id (A : Coalgebra G) : Hom A A where f := 𝟙 A.A

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {P Q R : Coalgebra G} (f : Hom P Q) (g : Hom Q R)
  body: f.f ≫ g.f

中文:
定义 comp
  签名: {P Q R : Coalgebra G} (f : Hom P Q) (g : Hom Q R)
  定义体: f.f ≫ g.f
-/
def comp {P Q R : Coalgebra G} (f : Hom P Q) (g : Hom Q R) : Hom P R where f := f.f ≫ g.f

end Hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryStruct (Coalgebra G)
  body: Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]

中文:
实例 :
  签名: CategoryStruct (Coalgebra G)
  定义体: Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
-/
instance : CategoryStruct (Coalgebra G) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
/--
lemma `Hom.ext'` / 引理 `Hom.ext'`

English:
lemma Hom.ext'
  given: (X Y : Coalgebra G) (f g : X ⟶ Y) (h : f.f = g.f)
  statement: f = g
  proof: Hom.ext h

@[simp]

中文:
引理 Hom.ext'
  条件: (X Y : Coalgebra G) (f g : X ⟶ Y) (h : f.f = g.f)
  结论: f = g
  证明: Hom.ext h

@[simp]
-/
lemma Hom.ext' (X Y : Coalgebra G) (f g : X ⟶ Y) (h : f.f = g.f) : f = g := Hom.ext h

@[simp]
/--
theorem `comp_eq_comp` / 定理 `comp_eq_comp`

English:
theorem comp_eq_comp
  given: {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'')
  proof: rfl

@[simp]

中文:
定理 comp_eq_comp
  条件: {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'')
  证明: rfl

@[simp]
-/
theorem comp_eq_comp {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') :
    Coalgebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
/--
theorem `id_eq_id` / 定理 `id_eq_id`

English:
theorem id_eq_id
  given: (A : Coalgebra G)
  statement: Coalgebra.Hom.id A = 𝟙 A
  proof: rfl

@[simp]

中文:
定理 id_eq_id
  条件: (A : Coalgebra G)
  结论: Coalgebra.Hom.id A = 𝟙 A
  证明: rfl

@[simp]
-/
theorem id_eq_id (A : Coalgebra G) : Coalgebra.Hom.id A = 𝟙 A :=
  rfl

@[simp]
/--
theorem `id_f` / 定理 `id_f`

English:
theorem id_f
  given: (A : Coalgebra G)
  statement: (𝟙 A : A ⟶ A).f = 𝟙 A.A
  proof: rfl

@[simp]

中文:
定理 id_f
  条件: (A : Coalgebra G)
  结论: (𝟙 A : A ⟶ A).f = 𝟙 A.A
  证明: rfl

@[simp]
-/
theorem id_f (A : Coalgebra G) : (𝟙 A : A ⟶ A).f = 𝟙 A.A :=
  rfl

@[simp]
/--
theorem `comp_f` / 定理 `comp_f`

English:
theorem comp_f
  given: {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'')
  statement: (f ≫ g).f = f.f ≫ g.f
  proof: rfl

中文:
定理 comp_f
  条件: {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'')
  结论: (f ≫ g).f = f.f ≫ g.f
  证明: rfl
-/
theorem comp_f {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') : (f ≫ g).f = f.f ≫ g.f :=
  rfl

/--
Instance `eilenbergMoore` / 实例 `eilenbergMoore`

English:
instance eilenbergMoore
  signature: : Category (Coalgebra G) where

中文:
实例 eilenbergMoore
  签名: : Category (Coalgebra G) where
-/
instance eilenbergMoore : Category (Coalgebra G) where

/--
To construct an isomorphism of coalgebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {A B : Coalgebra G} (h : A.A ≅ B.A)
  body: { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_inv_comp]; rw [← reassoc_of% w]; rw [← Functor.map_comp]
        simp }

中文:
定义 isoMk
  签名: {A B : Coalgebra G} (h : A.A ≅ B.A)
  定义体: { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_inv_comp]; rw [← reassoc_of% w]; rw [← Functor.map_comp]
        simp }

Depends on / 依赖: Functor, Functor.map_comp, cat_disch, eq_inv_comp, h.eq_inv_comp, h.hom, h.inv, map_comp, reassoc_of
-/
def isoMk {A B : Coalgebra G} (h : A.A ≅ B.A)
    (w : A.a ≫ (G : C ⥤ C).map h.hom = h.hom ≫ B.a := by cat_disch) : A ≅ B where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_inv_comp]; rw [← reassoc_of% w]; rw [← Functor.map_comp]
        simp }

end Coalgebra

variable (G : Comonad C)

/-- The forgetful functor from the Eilenberg-Moore category, forgetting the coalgebraic
structure. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Coalgebra G ⥤ C where
  body: A.A
  map f := f.f

中文:
定义 forget
  签名: : Coalgebra G ⥤ C where
  定义体: A.A
  map f := f.f
-/
def forget : Coalgebra G ⥤ C where
  obj A := A.A
  map f := f.f

/-- The cofree functor from the Eilenberg-Moore category, constructing a coalgebra for any
object. -/
@[simps]
/--
Definition of `cofree` / `cofree` 的定义

English:
definition cofree
  signature: : C ⥤ Coalgebra G where
  body: { A := G.obj X
      a := G.δ.app X
      coassoc := (G.coassoc _).symm }
  map f :=
    { f := G.map f
      h := (G.δ.naturality _).symm }

中文:
定义 cofree
  签名: : C ⥤ Coalgebra G where
  定义体: { A := G.obj X
      a := G.δ.app X
      coassoc := (G.coassoc _).symm }
  map f :=
    { f := G.map f
      h := (G.δ.naturality _).symm }

Depends on / 依赖: G.coassoc, G.map, G.obj, coassoc, naturality
-/
def cofree : C ⥤ Coalgebra G where
  obj X :=
    { A := G.obj X
      a := G.δ.app X
      coassoc := (G.coassoc _).symm }
  map f :=
    { f := G.map f
      h := (G.δ.naturality _).symm }

set_option backward.isDefEq.respectTransparency false in
-- The other two `simps` projection lemmas can be derived from these two, so `simp_nf` complains if
-- those are added too
/-- The adjunction between the cofree and forgetful constructions for Eilenberg-Moore coalgebras
for a comonad.
-/
@[simps! unit counit]
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : G.forget ⊣ G.cofree
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f =>
            { f := X.a ≫ G.map f
              h := by simp [← Coalgebra.coassoc_assoc] }
          invFun := fun g => g.f ≫ G.ε.app Y
          left_inv := fun f => by
            dsimp
            rw [Category.assoc];

中文:
定义 adj
  签名: : G.forget ⊣ G.cofree
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f =>
            { f := X.a ≫ G.map f
              h := by simp [← Coalgebra.coassoc_assoc] }
          invFun := fun g => g.f ≫ G.ε.app Y
          left_inv := fun f => by
            dsimp
            rw [Category.assoc];

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Category, Category.assoc, Coalgebra, Coalgebra.coassoc_assoc, Comonad, Comonad.right_counit, Functor, Functor.id_map, Functor.map_comp, G.map, X.counit_assoc, coassoc_assoc, cofree_obj_a, comp_id, counit_assoc, g.h_assoc, h_assoc, homEquiv
-/
def adj : G.forget ⊣ G.cofree :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f =>
            { f := X.a ≫ G.map f
              h := by simp [← Coalgebra.coassoc_assoc] }
          invFun := fun g => g.f ≫ G.ε.app Y
          left_inv := fun f => by
            dsimp
            rw [Category.assoc]; rw [G.ε.naturality]; rw [Functor.id_map]; rw [X.counit_assoc]
          right_inv := fun g => by
            ext1; dsimp
            rw [Functor.map_comp]; rw [g.h_assoc]; rw [cofree_obj_a]; rw [Comonad.right_counit]
            apply comp_id } }

/--
theorem `coalgebra_iso_of_iso` / 定理 `coalgebra_iso_of_iso`

English:
theorem coalgebra_iso_of_iso
  given: {A B : Coalgebra G} (f : A ⟶ B) [IsIso f.f]
  statement: IsIso f
  proof: ⟨⟨{ f := inv f.f
        h := by
          rw [IsIso.eq_inv_comp f.f]; rw [← f.h_assoc]
          simp },
      by cat_disch⟩⟩

中文:
定理 coalgebra_iso_of_iso
  条件: {A B : Coalgebra G} (f : A ⟶ B) [IsIso f.f]
  结论: IsIso f
  证明: ⟨⟨{ f := inv f.f
        h := by
          rw [IsIso.eq_inv_comp f.f]; rw [← f.h_assoc]
          simp },
      by cat_disch⟩⟩

Depends on / 依赖: IsIso.eq_inv_comp, cat_disch, eq_inv_comp, f.h_assoc, h_assoc
-/
theorem coalgebra_iso_of_iso {A B : Coalgebra G} (f : A ⟶ B) [IsIso f.f] : IsIso f :=
  ⟨⟨{ f := inv f.f
        h := by
          rw [IsIso.eq_inv_comp f.f]; rw [← f.h_assoc]
          simp },
      by cat_disch⟩⟩

/--
Instance `forget_reflects_iso` / 实例 `forget_reflects_iso`

English:
instance forget_reflects_iso
  signature: : G.forget.ReflectsIsomorphisms where
  body: coalgebra_iso_of_iso G f

中文:
实例 forget_reflects_iso
  签名: : G.forget.ReflectsIsomorphisms where
  定义体: coalgebra_iso_of_iso G f

Depends on / 依赖: coalgebra_iso_of_iso
-/
instance forget_reflects_iso : G.forget.ReflectsIsomorphisms where
  reflects {_ _} f [IsIso f.f] := coalgebra_iso_of_iso G f

/--
Instance `forget_faithful` / 实例 `forget_faithful`

English:
instance forget_faithful
  signature: : (forget G).Faithful where

中文:
实例 forget_faithful
  签名: : (forget G).Faithful where
-/
instance forget_faithful : (forget G).Faithful where

/--
theorem `algebra_epi_of_epi` / 定理 `algebra_epi_of_epi`

English:
theorem algebra_epi_of_epi
  given: {X Y : Coalgebra G} (f : X ⟶ Y) [h : Epi f.f]
  statement: Epi f
  proof: (forget G).epi_of_epi_map h

中文:
定理 algebra_epi_of_epi
  条件: {X Y : Coalgebra G} (f : X ⟶ Y) [h : Epi f.f]
  结论: Epi f
  证明: (forget G).epi_of_epi_map h

Depends on / 依赖: epi_of_epi_map, forget
-/
theorem algebra_epi_of_epi {X Y : Coalgebra G} (f : X ⟶ Y) [h : Epi f.f] : Epi f :=
  (forget G).epi_of_epi_map h

/--
theorem `algebra_mono_of_mono` / 定理 `algebra_mono_of_mono`

English:
theorem algebra_mono_of_mono
  given: {X Y : Coalgebra G} (f : X ⟶ Y) [h : Mono f.f]
  statement: Mono f
  proof: (forget G).mono_of_mono_map h

中文:
定理 algebra_mono_of_mono
  条件: {X Y : Coalgebra G} (f : X ⟶ Y) [h : Mono f.f]
  结论: Mono f
  证明: (forget G).mono_of_mono_map h

Depends on / 依赖: forget, mono_of_mono_map
-/
theorem algebra_mono_of_mono {X Y : Coalgebra G} (f : X ⟶ Y) [h : Mono f.f] : Mono f :=
  (forget G).mono_of_mono_map h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: G.forget.IsLeftAdjoint
  body: ⟨_, ⟨G.adj⟩⟩

中文:
实例 :
  签名: G.forget.IsLeftAdjoint
  定义体: ⟨_, ⟨G.adj⟩⟩

Depends on / 依赖: G.adj
-/
instance : G.forget.IsLeftAdjoint :=
  ⟨_, ⟨G.adj⟩⟩

end Comonad

end CategoryTheory
