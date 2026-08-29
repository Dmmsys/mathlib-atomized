/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.NatIso

/-!
# Disjoint union of categories

We define the category structure on a sigma-type (disjoint union) of categories.
-/

@[expose] public section


namespace CategoryTheory

namespace Sigma

universe w₁ w₂ w₃ v₁ v₂ u₁ u₂

variable {I : Type w₁} {C : I -> Type u₁} [forall i, Category.{v₁} (C i)]

/--
Inductive type `SigmaHom` / 归纳类型 `SigmaHom`

English:
inductive SigmaHom
  parameters: : (Σ i, C i) -> (Σ i, C i) -> Type max w₁ v₁ u₁
  constructors (1):
    - mk: forall {i : I} {X Y : C i}, (X ⟶ Y) -> SigmaHom ⟨i, X⟩ ⟨i, Y⟩

中文:
归纳类型 SigmaHom
  参数: : (Σ i, C i) -> (Σ i, C i) -> Type max w₁ v₁ u₁
  构造子 (1 个):
    - mk: 对任意 {i : I} {X Y : C i}, (X ⟶ Y) -> SigmaHom ⟨i, X⟩ ⟨i, Y⟩
-/
inductive SigmaHom : (Σ i, C i) -> (Σ i, C i) -> Type max w₁ v₁ u₁
  | mk : forall {i : I} {X Y : C i}, (X ⟶ Y) -> SigmaHom ⟨i, X⟩ ⟨i, Y⟩

namespace SigmaHom

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : forall X : Σ i, C i, SigmaHom X X

中文:
定义 id
  签名: : 对任意 X : Σ i, C i, SigmaHom X X
-/
def id : forall X : Σ i, C i, SigmaHom X X
  | ⟨_, _⟩ => mk (𝟙 _)

instance (X : Σ i, C i) : Inhabited (SigmaHom X X) :=
  ⟨id X⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: : forall {X Y Z : Σ i, C i}, SigmaHom X Y -> SigmaHom Y Z -> SigmaHom X Z

中文:
定义 comp
  签名: : 对任意 {X Y Z : Σ i, C i}, SigmaHom X Y -> SigmaHom Y Z -> SigmaHom X Z
-/
def comp : forall {X Y Z : Σ i, C i}, SigmaHom X Y -> SigmaHom Y Z -> SigmaHom X Z
  | _, _, _, mk f, mk g => mk (f ≫ g)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryStruct (Σ i, C i)
  body: SigmaHom
  id := id
  comp f g := comp f g

@[simp]

中文:
实例 :
  签名: CategoryStruct (Σ i, C i)
  定义体: SigmaHom
  id := id
  comp f g := comp f g

@[simp]

Depends on / 依赖: SigmaHom
-/
instance : CategoryStruct (Σ i, C i) where
  Hom := SigmaHom
  id := id
  comp f g := comp f g

@[simp]
/--
lemma `comp_def` / 引理 `comp_def`

English:
lemma comp_def
  given: (i : I) (X Y Z : C i) (f : X ⟶ Y) (g : Y ⟶ Z)
  statement: comp (mk f) (mk g) = mk (f ≫ g)
  proof: rfl

中文:
引理 comp_def
  条件: (i : I) (X Y Z : C i) (f : X ⟶ Y) (g : Y ⟶ Z)
  结论: comp (mk f) (mk g) = mk (f ≫ g)
  证明: rfl
-/
lemma comp_def (i : I) (X Y Z : C i) (f : X ⟶ Y) (g : Y ⟶ Z) : comp (mk f) (mk g) = mk (f ≫ g) :=
  rfl

/--
lemma `assoc` / 引理 `assoc`

English:
lemma assoc
  statement: forall {X Y Z W : Σ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W), (f ≫ g) ≫ h = f ≫ g ≫ h

中文:
引理 assoc
  结论: 对任意 {X Y Z W : Σ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W), (f ≫ g) ≫ h = f ≫ g ≫ h
-/
lemma assoc : forall {X Y Z W : Σ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W), (f ≫ g) ≫ h = f ≫ g ≫ h
  | _, _, _, _, mk _, mk _, mk _ => congr_arg mk (Category.assoc _ _ _)

/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  statement: forall {X Y : Σ i, C i} (f : X ⟶ Y), 𝟙 X ≫ f = f

中文:
引理 id_comp
  结论: 对任意 {X Y : Σ i, C i} (f : X ⟶ Y), 𝟙 X ≫ f = f
-/
lemma id_comp : forall {X Y : Σ i, C i} (f : X ⟶ Y), 𝟙 X ≫ f = f
  | _, _, mk _ => congr_arg mk (Category.id_comp _)

/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  statement: forall {X Y : Σ i, C i} (f : X ⟶ Y), f ≫ 𝟙 Y = f

中文:
引理 comp_id
  结论: 对任意 {X Y : Σ i, C i} (f : X ⟶ Y), f ≫ 𝟙 Y = f
-/
lemma comp_id : forall {X Y : Σ i, C i} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  | _, _, mk _ => congr_arg mk (Category.comp_id _)

end SigmaHom

/--
Instance `sigma` / 实例 `sigma`

English:
instance sigma
  signature: : Category (Σ i, C i) where
  body: SigmaHom.id_comp
  comp_id := SigmaHom.comp_id
  assoc := SigmaHom.assoc

中文:
实例 sigma
  签名: : Category (Σ i, C i) where
  定义体: SigmaHom.id_comp
  comp_id := SigmaHom.comp_id
  assoc := SigmaHom.assoc

Depends on / 依赖: SigmaHom, SigmaHom.id_comp, id_comp
-/
instance sigma : Category (Σ i, C i) where
  id_comp := SigmaHom.id_comp
  comp_id := SigmaHom.comp_id
  assoc := SigmaHom.assoc

/-- The inclusion functor into the disjoint union of categories. -/
@[simps map]
/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: (i : I)
  body: ⟨i, X⟩
  map := SigmaHom.mk

@[simp]

中文:
定义 incl
  签名: (i : I)
  定义体: ⟨i, X⟩
  map := SigmaHom.mk

@[simp]
-/
def incl (i : I) : C i ⥤ Σ i, C i where
  obj X := ⟨i, X⟩
  map := SigmaHom.mk

@[simp]
/--
lemma `incl_obj` / 引理 `incl_obj`

English:
lemma incl_obj
  given: {i : I} (X : C i)
  statement: (incl i).obj X = ⟨i, X⟩
  proof: rfl

中文:
引理 incl_obj
  条件: {i : I} (X : C i)
  结论: (incl i).obj X = ⟨i, X⟩
  证明: rfl
-/
lemma incl_obj {i : I} (X : C i) : (incl i).obj X = ⟨i, X⟩ :=
  rfl

instance (i : I) : Functor.Full (incl i : C i ⥤ Σ i, C i) where
  map_surjective := fun ⟨f⟩ => ⟨f, rfl⟩

instance (i : I) : Functor.Faithful (incl i : C i ⥤ Σ i, C i) where
  map_injective {_ _ _ _} h := by injection h

section

variable {D : Type u₂} [Category.{v₂} D] (F : forall i, C i ⥤ D)

/--
Definition of `natTrans` / `natTrans` 的定义

English:
definition natTrans
  signature: {F G : (Σ i, C i) ⥤ D} (h : forall i : I, incl i ⋙ F ⟶ incl i ⋙ G)
  body: fun ⟨j, X⟩ => (h j).app X
  naturality := by
    rintro ⟨j, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h j).naturality

@[simp]

中文:
定义 natTrans
  签名: {F G : (Σ i, C i) ⥤ D} (h : 对任意 i : I, incl i ⋙ F ⟶ incl i ⋙ G)
  定义体: fun ⟨j, X⟩ => (h j).app X
  naturality := by
    rintro ⟨j, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h j).naturality

@[simp]
-/
def natTrans {F G : (Σ i, C i) ⥤ D} (h : forall i : I, incl i ⋙ F ⟶ incl i ⋙ G) : F ⟶ G where
  app := fun ⟨j, X⟩ => (h j).app X
  naturality := by
    rintro ⟨j, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h j).naturality

@[simp]
/--
lemma `natTrans_app` / 引理 `natTrans_app`

English:
lemma natTrans_app
  statement: {F G : (Σ i, C i) ⥤ D} (h : forall i : I, incl i ⋙ F ⟶ incl i ⋙ G) (i : I)
  proof: rfl

中文:
引理 natTrans_app
  结论: {F G : (Σ i, C i) ⥤ D} (h : 对任意 i : I, incl i ⋙ F ⟶ incl i ⋙ G) (i : I)
  证明: rfl
-/
lemma natTrans_app {F G : (Σ i, C i) ⥤ D} (h : forall i : I, incl i ⋙ F ⟶ incl i ⋙ G) (i : I)
    (X : C i) : (natTrans h).app ⟨i, X⟩ = (h i).app X :=
  rfl

/--
Definition of `descMap` / `descMap` 的定义

English:
definition descMap
  signature: : forall X Y : Σ i, C i, (X ⟶ Y) -> ((F X.1).obj X.2 ⟶ (F Y.1).obj Y.2)

中文:
定义 descMap
  签名: : 对任意 X Y : Σ i, C i, (X ⟶ Y) -> ((F X.1).obj X.2 ⟶ (F Y.1).obj Y.2)
-/
def descMap : forall X Y : Σ i, C i, (X ⟶ Y) -> ((F X.1).obj X.2 ⟶ (F Y.1).obj Y.2)
  | _, _, SigmaHom.mk g => (F _).map g

/-- Given a collection of functors `F i : C i ⥤ D`, we can produce a functor `(Σ i, C i) ⥤ D`.

The produced functor `desc F` satisfies: `incl i ⋙ desc F ≅ F i`, i.e. restricted to just the
subcategory `C i`, `desc F` agrees with `F i`, and it is unique (up to natural isomorphism) with
this property.

This witnesses that the sigma-type is the coproduct in Cat.
-/
@[simps obj]
/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: : (Σ i, C i) ⥤ D where
  body: (F X.1).obj X.2
  map g := descMap F _ _ g
  map_id := by
    rintro ⟨i, X⟩
    apply (F i).map_id
  map_comp := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨_, Z⟩ ⟨f⟩ ⟨g⟩
    apply (F i).map_comp

@[simp]

中文:
定义 desc
  签名: : (Σ i, C i) ⥤ D where
  定义体: (F X.1).obj X.2
  map g := descMap F _ _ g
  map_id := by
    rintro ⟨i, X⟩
    apply (F i).map_id
  map_comp := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨_, Z⟩ ⟨f⟩ ⟨g⟩
    apply (F i).map_comp

@[simp]
-/
def desc : (Σ i, C i) ⥤ D where
  obj X := (F X.1).obj X.2
  map g := descMap F _ _ g
  map_id := by
    rintro ⟨i, X⟩
    apply (F i).map_id
  map_comp := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨_, Z⟩ ⟨f⟩ ⟨g⟩
    apply (F i).map_comp

@[simp]
/--
lemma `desc_map_mk` / 引理 `desc_map_mk`

English:
lemma desc_map_mk
  given: {i : I} (X Y : C i) (f : X ⟶ Y)
  statement: (desc F).map (SigmaHom.mk f) = (F i).map f
  proof: rfl

中文:
引理 desc_map_mk
  条件: {i : I} (X Y : C i) (f : X ⟶ Y)
  结论: (desc F).map (SigmaHom.mk f) = (F i).map f
  证明: rfl
-/
lemma desc_map_mk {i : I} (X Y : C i) (f : X ⟶ Y) : (desc F).map (SigmaHom.mk f) = (F i).map f :=
  rfl

set_option backward.defeqAttrib.useBackward true in
-- We hand-generate the simp lemmas about this since they come out cleaner.
/--
Definition of `inclDesc` / `inclDesc` 的定义

English:
definition inclDesc
  signature: (i : I)
  body: NatIso.ofComponents fun _ => Iso.refl _

@[simp]

中文:
定义 inclDesc
  签名: (i : I)
  定义体: NatIso.ofComponents fun _ => Iso.refl _

@[simp]

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def inclDesc (i : I) : incl i ⋙ desc F ≅ F i :=
  NatIso.ofComponents fun _ => Iso.refl _

@[simp]
/--
lemma `inclDesc_hom_app` / 引理 `inclDesc_hom_app`

English:
lemma inclDesc_hom_app
  given: (i : I) (X : C i)
  statement: (inclDesc F i).hom.app X = 𝟙 ((F i).obj X)
  proof: rfl

@[simp]

中文:
引理 inclDesc_hom_app
  条件: (i : I) (X : C i)
  结论: (inclDesc F i).hom.app X = 𝟙 ((F i).obj X)
  证明: rfl

@[simp]
-/
lemma inclDesc_hom_app (i : I) (X : C i) : (inclDesc F i).hom.app X = 𝟙 ((F i).obj X) :=
  rfl

@[simp]
/--
lemma `inclDesc_inv_app` / 引理 `inclDesc_inv_app`

English:
lemma inclDesc_inv_app
  given: (i : I) (X : C i)
  statement: (inclDesc F i).inv.app X = 𝟙 ((F i).obj X)
  proof: rfl

中文:
引理 inclDesc_inv_app
  条件: (i : I) (X : C i)
  结论: (inclDesc F i).inv.app X = 𝟙 ((F i).obj X)
  证明: rfl
-/
lemma inclDesc_inv_app (i : I) (X : C i) : (inclDesc F i).inv.app X = 𝟙 ((F i).obj X) :=
  rfl

/--
Definition of `descUniq` / `descUniq` 的定义

English:
definition descUniq
  signature: (q : (Σ i, C i) ⥤ D) (h : forall i, incl i ⋙ q ≅ F i)
  body: NatIso.ofComponents (fun ⟨i, X⟩ => (h i).app X) by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h i).hom.naturality f

@[simp]

中文:
定义 descUniq
  签名: (q : (Σ i, C i) ⥤ D) (h : 对任意 i, incl i ⋙ q ≅ F i)
  定义体: NatIso.ofComponents (fun ⟨i, X⟩ => (h i).app X) by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h i).hom.naturality f

@[simp]

Depends on / 依赖: NatIso, NatIso.ofComponents, hom.naturality, naturality, ofComponents
-/
def descUniq (q : (Σ i, C i) ⥤ D) (h : forall i, incl i ⋙ q ≅ F i) : q ≅ desc F :=
NatIso.ofComponents (fun ⟨i, X⟩ => (h i).app X) by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h i).hom.naturality f

@[simp]
/--
lemma `descUniq_hom_app` / 引理 `descUniq_hom_app`

English:
lemma descUniq_hom_app
  given: (q : (Σ i, C i) ⥤ D) (h : forall i, incl i ⋙ q ≅ F i) (i : I) (X : C i)
  proof: rfl

@[simp]

中文:
引理 descUniq_hom_app
  条件: (q : (Σ i, C i) ⥤ D) (h : 对任意 i, incl i ⋙ q ≅ F i) (i : I) (X : C i)
  证明: rfl

@[simp]
-/
lemma descUniq_hom_app (q : (Σ i, C i) ⥤ D) (h : forall i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).hom.app ⟨i, X⟩ = (h i).hom.app X :=
  rfl

@[simp]
/--
lemma `descUniq_inv_app` / 引理 `descUniq_inv_app`

English:
lemma descUniq_inv_app
  given: (q : (Σ i, C i) ⥤ D) (h : forall i, incl i ⋙ q ≅ F i) (i : I) (X : C i)
  proof: rfl

中文:
引理 descUniq_inv_app
  条件: (q : (Σ i, C i) ⥤ D) (h : 对任意 i, incl i ⋙ q ≅ F i) (i : I) (X : C i)
  证明: rfl
-/
lemma descUniq_inv_app (q : (Σ i, C i) ⥤ D) (h : forall i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).inv.app ⟨i, X⟩ = (h i).inv.app X :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
If `q₁` and `q₂` when restricted to each subcategory `C i` agree, then `q₁` and `q₂` are isomorphic.
-/
@[simps]
/--
Definition of `natIso` / `natIso` 的定义

English:
definition natIso
  signature: {q₁ q₂ : (Σ i, C i) ⥤ D} (h : forall i, incl i ⋙ q₁ ≅ incl i ⋙ q₂)
  body: natTrans fun i => (h i).hom
  inv := natTrans fun i => (h i).inv

中文:
定义 natIso
  签名: {q₁ q₂ : (Σ i, C i) ⥤ D} (h : 对任意 i, incl i ⋙ q₁ ≅ incl i ⋙ q₂)
  定义体: natTrans fun i => (h i).hom
  inv := natTrans fun i => (h i).inv

Depends on / 依赖: natTrans
-/
def natIso {q₁ q₂ : (Σ i, C i) ⥤ D} (h : forall i, incl i ⋙ q₁ ≅ incl i ⋙ q₂) : q₁ ≅ q₂ where
  hom := natTrans fun i => (h i).hom
  inv := natTrans fun i => (h i).inv

end

section

variable (C) {J : Type w₂} (g : J -> I)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : (Σ j : J, C (g j)) ⥤ Σ i : I, C i
  body: desc fun j => incl (g j)

@[simp]

中文:
定义 map
  签名: : (Σ j : J, C (g j)) ⥤ Σ i : I, C i
  定义体: desc fun j => incl (g j)

@[simp]
-/
def map : (Σ j : J, C (g j)) ⥤ Σ i : I, C i :=
  desc fun j => incl (g j)

@[simp]
/--
lemma `map_obj` / 引理 `map_obj`

English:
lemma map_obj
  given: (j : J) (X : C (g j))
  statement: (Sigma.map C g).obj ⟨j, X⟩ = ⟨g j, X⟩
  proof: rfl

@[simp]

中文:
引理 map_obj
  条件: (j : J) (X : C (g j))
  结论: (Sigma.map C g).obj ⟨j, X⟩ = ⟨g j, X⟩
  证明: rfl

@[simp]
-/
lemma map_obj (j : J) (X : C (g j)) : (Sigma.map C g).obj ⟨j, X⟩ = ⟨g j, X⟩ :=
  rfl

@[simp]
/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  given: {j : J} {X Y : C (g j)} (f : X ⟶ Y)
  proof: rfl

中文:
引理 map_map
  条件: {j : J} {X Y : C (g j)} (f : X ⟶ Y)
  证明: rfl
-/
lemma map_map {j : J} {X Y : C (g j)} (f : X ⟶ Y) :
    (Sigma.map C g).map (SigmaHom.mk f) = SigmaHom.mk f :=
  rfl

/-- The functor `Sigma.map C g` restricted to the subcategory `C j` acts as the inclusion of `g j`.
-/
@[simps!]
/--
Definition of `inclCompMap` / `inclCompMap` 的定义

English:
definition inclCompMap
  signature: (j : J)
  body: Iso.refl _

中文:
定义 inclCompMap
  签名: (j : J)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def inclCompMap (j : J) : incl j ⋙ map C g ≅ incl (g j) :=
  Iso.refl _

variable (I)

set_option backward.isDefEq.respectTransparency false in
/-- The functor `Sigma.map` applied to the identity function is just the identity functor. -/
@[simps!]
/--
Definition of `mapId` / `mapId` 的定义

English:
definition mapId
  signature: : map C (id : I -> I) ≅ 𝟭 (Σ i, C i)
  body: natIso fun i => NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 mapId
  签名: : map C (id : I -> I) ≅ 𝟭 (Σ i, C i)
  定义体: natIso fun i => NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, natIso, ofComponents
-/
def mapId : map C (id : I -> I) ≅ 𝟭 (Σ i, C i) :=
  natIso fun i => NatIso.ofComponents fun _ => Iso.refl _

variable {I} {K : Type w₃}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `Sigma.map` applied to a composition is a composition of functors. -/
@[simps!]
/--
Definition of `mapComp` / `mapComp` 的定义

English:
definition mapComp
  signature: (f : K -> J) (g : J -> I)
  body: (descUniq _ _) fun k =>
    (Functor.isoWhiskerRight (inclCompMap _ f k) (map C g :) :) ≪≫ inclCompMap _ g (f k)

中文:
定义 mapComp
  签名: (f : K -> J) (g : J -> I)
  定义体: (descUniq _ _) fun k =>
    (Functor.isoWhiskerRight (inclCompMap _ f k) (map C g :) :) ≪≫ inclCompMap _ g (f k)

Depends on / 依赖: Functor, Functor.isoWhiskerRight, descUniq, inclCompMap, isoWhiskerRight
-/
def mapComp (f : K -> J) (g : J -> I) : map (fun x => C (g x)) f ⋙ (map C g :) ≅ map C (g ∘ f) :=
  (descUniq _ _) fun k =>
    (Functor.isoWhiskerRight (inclCompMap _ f k) (map C g :) :) ≪≫ inclCompMap _ g (f k)

end

namespace Functor

-- variable {C}
variable {D : I -> Type u₁} [forall i, Category.{v₁} (D i)]

/--
Definition of `sigma` / `sigma` 的定义

English:
definition sigma
  signature: (F : forall i, C i ⥤ D i)
  body: desc fun i => F i ⋙ incl i

中文:
定义 sigma
  签名: (F : 对任意 i, C i ⥤ D i)
  定义体: desc fun i => F i ⋙ incl i
-/
def sigma (F : forall i, C i ⥤ D i) : (Σ i, C i) ⥤ Σ i, D i :=
  desc fun i => F i ⋙ incl i

end Functor

namespace natTrans

variable {D : I -> Type u₁} [forall i, Category.{v₁} (D i)]
variable {F G : forall i, C i ⥤ D i}

/--
Definition of `sigma` / `sigma` 的定义

English:
definition sigma
  signature: (α : forall i, F i ⟶ G i)
  body: SigmaHom.mk ((α f.1).app _)
  naturality := by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    change SigmaHom.mk _ = SigmaHom.mk _
    rw [(α i).naturality]

中文:
定义 sigma
  签名: (α : 对任意 i, F i ⟶ G i)
  定义体: SigmaHom.mk ((α f.1).app _)
  naturality := by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    change SigmaHom.mk _ = SigmaHom.mk _
    rw [(α i).naturality]

Depends on / 依赖: SigmaHom, SigmaHom.mk
-/
def sigma (α : forall i, F i ⟶ G i) : Functor.sigma F ⟶ Functor.sigma G where
  app f := SigmaHom.mk ((α f.1).app _)
  naturality := by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    change SigmaHom.mk _ = SigmaHom.mk _
    rw [(α i).naturality]

end natTrans

end Sigma

end CategoryTheory
