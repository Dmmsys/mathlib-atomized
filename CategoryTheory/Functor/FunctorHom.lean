/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Internal hom in functor categories

Given functors `F G : C ⥤ D`, define a functor `functorHom F G` from `C` to `Type max v' v u`,
which is a proxy for the "internal hom" functor Hom(F ⊗ coyoneda(-), G). This is used to show
that the functor category `C ⥤ D` is enriched over `C ⥤ Type max v' v u`. This is also useful
for showing that `C ⥤ Type max w v u` is monoidal closed.

See `Mathlib/CategoryTheory/Closed/FunctorToTypes.lean`.

-/

@[expose] public section


universe w v' v u u'

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (F G : C ⥤ D)

namespace CategoryTheory.Functor

/-- Given functors `F G : C ⥤ D`, `HomObj F G A` is a proxy for the type
of "morphisms" `F ⊗ A ⟶ G`, where `A : C ⥤ Type w` (`w` an arbitrary universe). -/
@[ext]
/--
Definition of `HomObj` / `HomObj` 的定义

English:
structure HomObj
  parameters: (A : C ⥤ Type w)
  axioms and operations (2):
    - app((c : C) (a : A.obj c)) : F.obj c ⟶ G.obj c
    - naturality({c d : C} (f : c ⟶ d) (a : A.obj c)) : F.map f ≫ app d (A.map f a) = app c a ≫ G.map f  [default: by cat_disch]

中文:
结构 HomObj
  参数: (A : C ⥤ 类型 w)
  公理与运算 (2 个):
    - app((c : C) (a : A.obj c)) : F.obj c ⟶ G.obj c
    - naturality({c d : C} (f : c ⟶ d) (a : A.obj c)) : F.map f ≫ app d (A.map f a) = app c a ≫ G.map f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure HomObj (A : C ⥤ Type w) where
  /-- The morphism `F.obj c ⟶ G.obj c` associated with `a : A.obj c`. -/
  app (c : C) (a : A.obj c) : F.obj c ⟶ G.obj c
  naturality {c d : C} (f : c ⟶ d) (a : A.obj c) :
    F.map f ≫ app d (A.map f a) = app c a ≫ G.map f := by cat_disch

/-- When `F`, `G`, and `A` are all functors `C ⥤ Type w`, then `HomObj F G A` is in
bijection with `F ⊗ A ⟶ G`. -/
@[simps]
/--
Definition of `homObjEquiv` / `homObjEquiv` 的定义

English:
definition homObjEquiv
  signature: (F G A : C ⥤ Type w)
  body: ⟨fun X => ↾fun ⟨x, y⟩ => a.app X y x, fun X Y f => by
    ext ⟨x, y⟩
    simpa using! ConcreteCategory.congr_hom (a.naturality f y) x⟩
  invFun a := ⟨fun X y => ↾fun x => a.app X (x, y), fun φ y => by
    ext x
    simpa using! (a.naturality_apply φ) (x, y)⟩
  left_inv _ := by aesop
  right_inv _ :=

中文:
定义 homObjEquiv
  签名: (F G A : C ⥤ 类型 w)
  定义体: ⟨fun X => ↾fun ⟨x, y⟩ => a.app X y x, fun X Y f => by
    ext ⟨x, y⟩
    simpa using! ConcreteCategory.congr_hom (a.naturality f y) x⟩
  invFun a := ⟨fun X y => ↾fun x => a.app X (x, y), fun φ y => by
    ext x
    simpa using! (a.naturality_apply φ) (x, y)⟩
  left_inv _ := by aesop
  right_inv _ :=

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, a.app, a.naturality, a.naturality_apply, congr_hom, invFun, left_inv, naturality, naturality_apply, right_inv
-/
def homObjEquiv (F G A : C ⥤ Type w) : (HomObj F G A) ≃ (F otimes A ⟶ G) where
  toFun a := ⟨fun X => ↾fun ⟨x, y⟩ => a.app X y x, fun X Y f => by
    ext ⟨x, y⟩
    simpa using! ConcreteCategory.congr_hom (a.naturality f y) x⟩
  invFun a := ⟨fun X y => ↾fun x => a.app X (x, y), fun φ y => by
    ext x
    simpa using! (a.naturality_apply φ) (x, y)⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

namespace HomObj

attribute [reassoc (attr := simp)] naturality

variable {F G} {A : C ⥤ Type w}

/--
lemma `congr_app` / 引理 `congr_app`

English:
lemma congr_app
  statement: {f g : HomObj F G A} (h : f = g) (X : C)
  proof: by subst h; rfl

中文:
引理 congr_app
  结论: {f g : HomObj F G A} (h : f = g) (X : C)
  证明: by subst h; rfl
-/
lemma congr_app {f g : HomObj F G A} (h : f = g) (X : C)
    (a : A.obj X) : f.app X a = g.app X a := by subst h; rfl

/-- Given a natural transformation `F ⟶ G`, get a term of `HomObj F G A` by "ignoring" `A`. -/
@[simps]
/--
Definition of `ofNatTrans` / `ofNatTrans` 的定义

English:
definition ofNatTrans
  signature: (f : F ⟶ G)
  body: f.app X

中文:
定义 of自然数Trans
  签名: (f : F ⟶ G)
  定义体: f.app X

Depends on / 依赖: HasImage, f.app, f.hom, g.hom, hasImageMapOfIsIso
-/
def ofNatTrans (f : F ⟶ G) : HomObj F G A where
  app X _ := f.app X

/-- The identity `HomObj F F A`. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (A : C ⥤ Type w)
  body: ofNatTrans (𝟙 F)

中文:
定义 id
  签名: (A : C ⥤ 类型 w)
  定义体: ofNatTrans (𝟙 F)

Depends on / 依赖: ofNatTrans
-/
def id (A : C ⥤ Type w) : HomObj F F A := ofNatTrans (𝟙 F)

/-- Composition of `f : HomObj F G A` with `g : HomObj G M A`. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {M : C ⥤ D} (f : HomObj F G A) (g : HomObj G M A)
  body: f.app X a ≫ g.app X a

中文:
定义 comp
  签名: {M : C ⥤ D} (f : HomObj F G A) (g : HomObj G M A)
  定义体: f.app X a ≫ g.app X a

Depends on / 依赖: f.app, g.app
-/
def comp {M : C ⥤ D} (f : HomObj F G A) (g : HomObj G M A) : HomObj F M A where
  app X a := f.app X a ≫ g.app X a

/-- Given a morphism `A' ⟶ A`, send a term of `HomObj F G A` to a term of `HomObj F G A'`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {A' : C ⥤ Type w} (f : A' ⟶ A) (x : HomObj F G A)
  body: x.app Δ (f.app Δ a)
  naturality {Δ Δ'} φ a := by
    rw [← x.naturality φ (f.app Δ a)]; rw [f.naturality_apply φ a]

中文:
定义 map
  签名: {A' : C ⥤ 类型 w} (f : A' ⟶ A) (x : HomObj F G A)
  定义体: x.app Δ (f.app Δ a)
  naturality {Δ Δ'} φ a := by
    rw [← x.naturality φ (f.app Δ a)]; rw [f.naturality_apply φ a]

Depends on / 依赖: f.app, x.app
-/
def map {A' : C ⥤ Type w} (f : A' ⟶ A) (x : HomObj F G A) : HomObj F G A' where
  app Δ a := x.app Δ (f.app Δ a)
  naturality {Δ Δ'} φ a := by
    rw [← x.naturality φ (f.app Δ a)]; rw [f.naturality_apply φ a]

end HomObj

/-- The contravariant functor taking `A : C ⥤ Type w` to `HomObj F G A`, i.e. Hom(F ⊗ -, G). -/
@[simps obj map]
/--
Definition of `homObjFunctor` / `homObjFunctor` 的定义

English:
definition homObjFunctor
  signature: : (C ⥤ Type w)ᵒᵖ ⥤ Type (max w v' u) where
  body: HomObj F G A.unop
  map {A A'} f := ↾fun x =>
    { app := fun X a => x.app X (f.unop.app _ a)
      naturality := fun {X Y} φ a => by
        rw [← HomObj.naturality]
        congr 2
        exact ConcreteCategory.congr_hom (f.unop.naturality φ) a }

中文:
定义 homObjFunctor
  签名: : (C ⥤ 类型 w)ᵒᵖ ⥤ 类型 (最大值 w v' u) where
  定义体: HomObj F G A.unop
  map {A A'} f := ↾fun x =>
    { app := fun X a => x.app X (f.unop.app _ a)
      naturality := fun {X Y} φ a => by
        rw [← HomObj.naturality]
        congr 2
        exact ConcreteCategory.congr_hom (f.unop.naturality φ) a }

Depends on / 依赖: A.unop, HomObj
-/
def homObjFunctor : (C ⥤ Type w)ᵒᵖ ⥤ Type (max w v' u) where
  obj A := HomObj F G A.unop
  map {A A'} f := ↾fun x =>
    { app := fun X a => x.app X (f.unop.app _ a)
      naturality := fun {X Y} φ a => by
        rw [← HomObj.naturality]
        congr 2
        exact ConcreteCategory.congr_hom (f.unop.naturality φ) a }

/--
Definition of `functorHom` / `functorHom` 的定义

English:
abbreviation functorHom
  signature: (F G : C ⥤ D)
  body: coyoneda.rightOp ⋙ homObjFunctor.{v} F G

中文:
缩写 functorHom
  签名: (F G : C ⥤ D)
  定义体: coyoneda.rightOp ⋙ homObjFunctor.{v} F G

Depends on / 依赖: coyoneda, coyoneda.rightOp, homObjFunctor, rightOp
-/
abbrev functorHom (F G : C ⥤ D) : C ⥤ Type (max v' v u) :=
  coyoneda.rightOp ⋙ homObjFunctor.{v} F G

variable {F G} in
@[ext]
/--
lemma `functorHom_ext` / 引理 `functorHom_ext`

English:
lemma functorHom_ext
  statement: {X : C} {x y : (F.functorHom G).obj X}
  proof: HomObj.ext (by ext; apply h)

中文:
引理 functorHom_ext
  结论: {X : C} {x y : (F.functorHom G).obj X}
  证明: HomObj.ext (by ext; apply h)

Depends on / 依赖: HomObj, HomObj.ext
-/
lemma functorHom_ext {X : C} {x y : (F.functorHom G).obj X}
    (h : forall (Y : C) (f : X ⟶ Y), x.app Y f = y.app Y f) : x = y :=
  HomObj.ext (by ext; apply h)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The equivalence `(A ⟶ F.functorHom G) ≃ HomObj F G A`. -/
@[simps]
/--
Definition of `functorHomEquiv` / `functorHomEquiv` 的定义

English:
definition functorHomEquiv
  signature: (A : C ⥤ Type (max u v v'))
  body: { app := fun X a => (φ.app X a).app X (𝟙 _)
      naturality := fun {X Y} f a => by
        rw [← (φ.app X a).naturality f (𝟙 _)]
        have := HomObj.congr_app (ConcreteCategory.congr_hom (φ.naturality f) a) Y (𝟙 _)
        simp_all [-NatTrans.naturality, functorHom, homObjFunctor] }
  invFun x :

中文:
定义 functorHomEquiv
  签名: (A : C ⥤ 类型 (最大值 u v v'))
  定义体: { app := fun X a => (φ.app X a).app X (𝟙 _)
      naturality := fun {X Y} f a => by
        rw [← (φ.app X a).naturality f (𝟙 _)]
        have := HomObj.congr_app (ConcreteCategory.congr_hom (φ.naturality f) a) Y (𝟙 _)
        simp_all [-NatTrans.naturality, functorHom, homObjFunctor] }
  invFun x :

Depends on / 依赖: A.map, ConcreteCategory, ConcreteCategory.congr_hom, HomObj, HomObj.congr_app, NatTrans, NatTrans.naturality, congr_app, congr_hom, functorHom, homObjFunctor, invFun, left_inv, naturality, x.app
-/
def functorHomEquiv (A : C ⥤ Type (max u v v')) : (A ⟶ F.functorHom G) ≃ HomObj F G A where
  toFun φ :=
    { app := fun X a => (φ.app X a).app X (𝟙 _)
      naturality := fun {X Y} f a => by
        rw [← (φ.app X a).naturality f (𝟙 _)]
        have := HomObj.congr_app (ConcreteCategory.congr_hom (φ.naturality f) a) Y (𝟙 _)
        simp_all [-NatTrans.naturality, functorHom, homObjFunctor] }
  invFun x :=
    { app X := ↾fun a => { app := fun Y f => x.app Y (A.map f a) }
      naturality X Y f := by
        ext
        simp [functorHom, homObjFunctor] }
  left_inv φ := by
    ext X a Y f
    exact (HomObj.congr_app (ConcreteCategory.congr_hom (φ.naturality f) a) Y (𝟙 _)).trans
      (congr_arg ((φ.app X a).app Y) (by simp))
  right_inv x := by simp [functorHom, homObjFunctor]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {F G} in
/-- Morphisms `(𝟙_ (C ⥤ Type max v' v u) ⟶ F.functorHom G)` are in bijection with
morphisms `F ⟶ G`. -/
@[simps]
/--
Definition of `natTransEquiv` / `natTransEquiv` 的定义

English:
definition natTransEquiv
  signature: : (𝟙_ (C ⥤ Type (max v' v u)) ⟶ F.functorHom G) ≃ (F ⟶ G) where
  body: ⟨fun X => (f.app X (PUnit.unit)).app X (𝟙 _), by
    intro X Y φ
    rw [← (f.app X (PUnit.unit)).naturality φ]
    congr 1
    have := HomObj.congr_app (ConcreteCategory.congr_hom (f.naturality φ) PUnit.unit) Y (𝟙 Y)
    dsimp [functorHom, homObjFunctor] at this
    aesop ⟩
  invFun f := { app _ :=

中文:
定义 natTransEquiv
  签名: : (𝟙_ (C ⥤ 类型 (最大值 v' v u)) ⟶ F.functorHom G) ≃ (F ⟶ G) where
  定义体: ⟨fun X => (f.app X (PUnit.unit)).app X (𝟙 _), by
    intro X Y φ
    rw [← (f.app X (PUnit.unit)).naturality φ]
    congr 1
    have := HomObj.congr_app (ConcreteCategory.congr_hom (f.naturality φ) PUnit.unit) Y (𝟙 Y)
    dsimp [functorHom, homObjFunctor] at this
    aesop ⟩
  invFun f := { app _ :=

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, HomObj, HomObj.congr_app, HomObj.ofNatTrans, PUnit.unit, congr_app, congr_hom, f.app, f.naturality, functorHom, homObjFunctor, invFun, left_inv, naturality, ofNatTrans
-/
def natTransEquiv : (𝟙_ (C ⥤ Type (max v' v u)) ⟶ F.functorHom G) ≃ (F ⟶ G) where
  toFun f := ⟨fun X => (f.app X (PUnit.unit)).app X (𝟙 _), by
    intro X Y φ
    rw [← (f.app X (PUnit.unit)).naturality φ]
    congr 1
    have := HomObj.congr_app (ConcreteCategory.congr_hom (f.naturality φ) PUnit.unit) Y (𝟙 Y)
    dsimp [functorHom, homObjFunctor] at this
    aesop ⟩
  invFun f := { app _ := ↾fun _ => HomObj.ofNatTrans f }
  left_inv f := by
    ext X a Y φ
    have := HomObj.congr_app (ConcreteCategory.congr_hom (f.naturality φ) PUnit.unit) Y (𝟙 Y)
    dsimp [functorHom, homObjFunctor] at this
    aesop

end CategoryTheory.Functor

open Functor

namespace CategoryTheory.Enriched.Functor

@[simp]
/--
lemma `natTransEquiv_symm_app_app_apply` / 引理 `natTransEquiv_symm_app_app_apply`

English:
lemma natTransEquiv_symm_app_app_apply
  statement: (F G : C ⥤ D) (f : F ⟶ G)
  proof: rfl

@[simp]

中文:
引理 natTransEquiv_symm_app_app_apply
  结论: (F G : C ⥤ D) (f : F ⟶ G)
  证明: rfl

@[simp]
-/
lemma natTransEquiv_symm_app_app_apply (F G : C ⥤ D) (f : F ⟶ G)
    {X : C} {a : (𝟙_ (C ⥤ Type (max v' v u))).obj X} (Y : C) {φ : X ⟶ Y} :
    dsimp% ((natTransEquiv.symm f).app X a).app Y φ = f.app Y := rfl

@[simp]
/--
lemma `natTransEquiv_symm_whiskerRight_functorHom_app` / 引理 `natTransEquiv_symm_whiskerRight_functorHom_app`

English:
lemma natTransEquiv_symm_whiskerRight_functorHom_app
  statement: (K L : C ⥤ D) (X : C) (f : K ⟶ K)
  proof: rfl

@[simp]

中文:
引理 natTransEquiv_symm_whiskerRight_functorHom_app
  结论: (K L : C ⥤ D) (X : C) (f : K ⟶ K)
  证明: rfl

@[simp]
-/
lemma natTransEquiv_symm_whiskerRight_functorHom_app (K L : C ⥤ D) (X : C) (f : K ⟶ K)
    (x : 𝟙_ _ otimes (K.functorHom L).obj X) :
    dsimp% (natTransEquiv.symm f ▷ K.functorHom L).app X x =
    (HomObj.ofNatTrans f, x.2) := rfl

@[simp]
/--
lemma `functorHom_whiskerLeft_natTransEquiv_symm_app` / 引理 `functorHom_whiskerLeft_natTransEquiv_symm_app`

English:
lemma functorHom_whiskerLeft_natTransEquiv_symm_app
  statement: (K L : C ⥤ D) (X : C) (f : L ⟶ L)
  proof: rfl

@[simp]

中文:
引理 functorHom_whiskerLeft_natTransEquiv_symm_app
  结论: (K L : C ⥤ D) (X : C) (f : L ⟶ L)
  证明: rfl

@[simp]
-/
lemma functorHom_whiskerLeft_natTransEquiv_symm_app (K L : C ⥤ D) (X : C) (f : L ⟶ L)
    (x : (K.functorHom L).obj X otimes 𝟙_ _) :
    dsimp% (K.functorHom L ◁ natTransEquiv.symm f).app X x =
    (x.1, HomObj.ofNatTrans f) := rfl

@[simp]
/--
lemma `whiskerLeft_app_apply` / 引理 `whiskerLeft_app_apply`

English:
lemma whiskerLeft_app_apply
  statement: (K L M N : C ⥤ D)
  proof: rfl

@[simp]

中文:
引理 whiskerLeft_app_apply
  结论: (K L M N : C ⥤ D)
  证明: rfl

@[simp]
-/
lemma whiskerLeft_app_apply (K L M N : C ⥤ D)
    (g : L.functorHom M otimes M.functorHom N ⟶ L.functorHom N)
    {X : C} (a : (K.functorHom L otimes L.functorHom M otimes M.functorHom N).obj X) :
    dsimp% (K.functorHom L ◁ g).app X a = ⟨a.1, g.app X a.2⟩ := rfl

@[simp]
/--
lemma `whiskerRight_app_apply` / 引理 `whiskerRight_app_apply`

English:
lemma whiskerRight_app_apply
  statement: (K L M N : C ⥤ D)
  proof: rfl

@[simp]

中文:
引理 whiskerRight_app_apply
  结论: (K L M N : C ⥤ D)
  证明: rfl

@[simp]
-/
lemma whiskerRight_app_apply (K L M N : C ⥤ D)
    (f : K.functorHom L otimes L.functorHom M ⟶ K.functorHom M)
    {X : C} (a : ((K.functorHom L otimes L.functorHom M) otimes M.functorHom N).obj X) :
    dsimp% (f ▷ M.functorHom N).app X a = ⟨f.app X a.1, a.2⟩ := rfl

@[simp]
/--
lemma `associator_inv_apply` / 引理 `associator_inv_apply`

English:
lemma associator_inv_apply
  statement: (K L M N : C ⥤ D) {X : C}
  proof: rfl

@[simp]

中文:
引理 associator_inv_apply
  结论: (K L M N : C ⥤ D) {X : C}
  证明: rfl

@[simp]
-/
lemma associator_inv_apply (K L M N : C ⥤ D) {X : C}
    (x : ((K.functorHom L) otimes (L.functorHom M) otimes (M.functorHom N)).obj X) :
    dsimp% (α_ ((K.functorHom L).obj X) ((L.functorHom M).obj X) ((M.functorHom N).obj X)).inv x =
    ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := rfl

@[simp]
/--
lemma `associator_hom_apply` / 引理 `associator_hom_apply`

English:
lemma associator_hom_apply
  statement: (K L M N : C ⥤ D) {X : C}
  proof: rfl

中文:
引理 associator_hom_apply
  结论: (K L M N : C ⥤ D) {X : C}
  证明: rfl
-/
lemma associator_hom_apply (K L M N : C ⥤ D) {X : C}
    (x : (((K.functorHom L) otimes (L.functorHom M)) otimes (M.functorHom N)).obj X) :
    dsimp% (α_ ((K.functorHom L).obj X) ((L.functorHom M).obj X) ((M.functorHom N).obj X)).hom x =
    ⟨x.1.1, x.1.2, x.2⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
attribute [local simp] functorHom types_tensorObj_def in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EnrichedCategory (C ⥤ Type (max v' v u)) (C ⥤ D)
  body: functorHom
  id F := natTransEquiv.symm (𝟙 F)
  comp F G H := { app _ := ↾fun f => f.1.comp f.2 }

中文:
实例 :
  签名: Enriched范畴 (C ⥤ 类型 (最大值 v' v u)) (C ⥤ D)
  定义体: functorHom
  id F := natTransEquiv.symm (𝟙 F)
  comp F G H := { app _ := ↾fun f => f.1.comp f.2 }

Depends on / 依赖: functorHom
-/
instance : EnrichedCategory (C ⥤ Type (max v' v u)) (C ⥤ D) where
  Hom := functorHom
  id F := natTransEquiv.symm (𝟙 F)
  comp F G H := { app _ := ↾fun f => f.1.comp f.2 }

end CategoryTheory.Enriched.Functor
