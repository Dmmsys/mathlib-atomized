/-
Copyright (c) 2025 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
module

public import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Free groupoid on a category

This file defines the free groupoid on a category, the lifting of a functor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given a type `C` and a category instance on `C`:

- `CategoryTheory.FreeGroupoid C`: the underlying type of the free groupoid on `C`.
- `CategoryTheory.FreeGroupoid.instGroupoid`: the `Groupoid` instance on `FreeGroupoid C`.
- `CategoryTheory.FreeGroupoid.lift`: the lifting of a functor `C ⥤ G` where `G` is a
  groupoid, to a functor `CategoryTheory.FreeGroupoid C ⥤ G`.
- `CategoryTheory.FreeGroupoid.lift_spec` and
  `CategoryTheory.FreeGroupoid.lift_unique`:
  the proofs that, respectively, `CategoryTheory.FreeGroupoid.lift` indeed is a lifting
  and is the unique one.
- `CategoryTheory.Grpd.free`: the free functor from `Grpd` to `Cat`
- `CategoryTheory.Grpd.freeForgetAdjunction`: that `free` is left adjoint to
  `Grpd.forgetToCat`.

## Implementation notes

The free groupoid on a category `C` is first defined by taking the free groupoid `G`
on the underlying *quiver* of `C`. Then the free groupoid on the *category* `C` is defined as
the quotient of `G` by the relation that makes the inclusion prefunctor `C ⥤q G` a functor.

-/

@[expose] public section

noncomputable section

namespace CategoryTheory

universe v u v₁ u₁ v₂ u₂

variable (C : Type u) [Category.{v} C]

open Quiver in
/--
Inductive type `FreeGroupoid.homRel` / 归纳类型 `FreeGroupoid.homRel`

English:
inductive FreeGroupoid.homRel
  parameters: : HomRel (Quiver.FreeGroupoid C) where
  constructors (2):
    - map_id: (X : C) : homRel ((FreeGroupoid.of C).map (𝟙 X)) (𝟙 ((FreeGroupoid.of C).obj X))
    - map_comp: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : homRel ((FreeGroupoid.of C).map (f ≫ g)) ((FreeGroupoid.of C).map f ≫ (FreeGroupoid.of C).map g)

中文:
归纳类型 FreeGroupoid.homRel
  参数: : HomRel (箭图.FreeGroupoid C) where
  构造子 (2 个):
    - map_id: (X : C) : homRel ((FreeGroupoid.of C).map (𝟙 X)) (𝟙 ((FreeGroupoid.of C).obj X))
    - map_comp: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : homRel ((FreeGroupoid.of C).map (f ≫ g)) ((FreeGroupoid.of C).map f ≫ (FreeGroupoid.of C).map g)
-/
inductive FreeGroupoid.homRel : HomRel (Quiver.FreeGroupoid C) where
| map_id (X : C) : homRel ((FreeGroupoid.of C).map (𝟙 X)) (𝟙 ((FreeGroupoid.of C).obj X))
| map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : homRel ((FreeGroupoid.of C).map (f ≫ g))
  ((FreeGroupoid.of C).map f ≫ (FreeGroupoid.of C).map g)

/--
Definition of `FreeGroupoid` / `FreeGroupoid` 的定义

English:
definition FreeGroupoid
  body: Quotient (FreeGroupoid.homRel C)

中文:
定义 FreeGroupoid
  定义体: Quotient (FreeGroupoid.homRel C)

Depends on / 依赖: FreeGroupoid, FreeGroupoid.homRel, Quotient, homRel
-/
def FreeGroupoid := Quotient (FreeGroupoid.homRel C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: C] : Nonempty (FreeGroupoid C)
  body: ⟨Quotient.mk (Quotient.mk ((Paths.of _).obj (Classical.arbitrary C)))⟩

中文:
实例 [非空
  签名: C] : 非空 (FreeGroupoid C)
  定义体: ⟨Quotient.mk (Quotient.mk ((Paths.of _).obj (Classical.arbitrary C)))⟩

Depends on / 依赖: Classical, Classical.arbitrary, Paths.of, Quotient, Quotient.mk, arbitrary
-/
instance [Nonempty C] : Nonempty (FreeGroupoid C) :=
  ⟨Quotient.mk (Quotient.mk ((Paths.of _).obj (Classical.arbitrary C)))⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Groupoid (FreeGroupoid C)
  body: Quotient.groupoid (FreeGroupoid.homRel C)

中文:
实例 :
  签名: 群胚 (FreeGroupoid C)
  定义体: Quotient.groupoid (FreeGroupoid.homRel C)

Depends on / 依赖: FreeGroupoid, FreeGroupoid.homRel, Quotient, Quotient.groupoid, groupoid, homRel
-/
instance : Groupoid (FreeGroupoid C) :=
  Quotient.groupoid (FreeGroupoid.homRel C)

namespace FreeGroupoid

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : C ⥤ FreeGroupoid C where
  body: Quiver.FreeGroupoid.of C ⋙q (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor
  map_id X := Quotient.sound _ (FreeGroupoid.homRel.map_id X)
  map_comp f g := Quotient.sound _ (FreeGroupoid.homRel.map_comp f g)

中文:
定义 of
  签名: : C ⥤ FreeGroupoid C where
  定义体: Quiver.FreeGroupoid.of C ⋙q (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor
  map_id X := Quotient.sound _ (FreeGroupoid.homRel.map_id X)
  map_comp f g := Quotient.sound _ (FreeGroupoid.homRel.map_comp f g)

Depends on / 依赖: FreeGroupoid, FreeGroupoid.homRel, Quiver, Quiver.FreeGroupoid.of, Quotient, Quotient.functor, functor, homRel, toPrefunctor
-/
def of : C ⥤ FreeGroupoid C where
  __ := Quiver.FreeGroupoid.of C ⋙q (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor
  map_id X := Quotient.sound _ (FreeGroupoid.homRel.map_id X)
  map_comp f g := Quotient.sound _ (FreeGroupoid.homRel.map_comp f g)

variable {C}

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (X : C)
  body: (of C).obj X

中文:
缩写 mk
  签名: (X : C)
  定义体: (of C).obj X
-/
abbrev mk (X : C) : FreeGroupoid C := (of C).obj X

/--
Definition of `homMk` / `homMk` 的定义

English:
abbreviation homMk
  signature: {X Y : C} (f : X ⟶ Y)
  body: (of C).map f

中文:
缩写 homMk
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: (of C).map f
-/
abbrev homMk {X Y : C} (f : X ⟶ Y) : mk X ⟶ mk Y := (of C).map f

/--
lemma `eq_mk` / 引理 `eq_mk`

English:
lemma eq_mk
  given: (X : FreeGroupoid C)
  statement: X = .mk (X.as.as)
  proof: rfl

中文:
引理 eq_mk
  条件: (X : FreeGroupoid C)
  结论: X = .mk (X.as.as)
  证明: rfl
-/
lemma eq_mk (X : FreeGroupoid C) : X = .mk (X.as.as) := rfl

/--
lemma `of_obj_bijective` / 引理 `of_obj_bijective`

English:
lemma of_obj_bijective
  statement: Function.Bijective (of C).obj where
  proof: by cases h; rfl
  right X := ⟨X.as.as, rfl⟩

中文:
引理 of_obj_bijective
  结论: 函数.双射 (of C).obj where
  证明: by cases h; rfl
  right X := ⟨X.as.as, rfl⟩

Depends on / 依赖: X.as.as
-/
lemma of_obj_bijective : Function.Bijective (of C).obj where
  left _ _ h := by cases h; rfl
  right X := ⟨X.as.as, rfl⟩

section UniversalProperty

variable {G : Type u₁} [Groupoid.{v₁} G]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (φ : C ⥤ G)
  body: Quotient.lift (FreeGroupoid.homRel C) (Quiver.FreeGroupoid.lift φ.toPrefunctor)
    (fun _ _ f g r => by
      have {X Y : C} (f : X ⟶ Y) :=
        Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec φ.toPrefunctor) f
      induction r <;> cat_disch)

中文:
定义 lift
  签名: (φ : C ⥤ G)
  定义体: Quotient.lift (FreeGroupoid.homRel C) (Quiver.FreeGroupoid.lift φ.toPrefunctor)
    (fun _ _ f g r => by
      have {X Y : C} (f : X ⟶ Y) :=
        Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec φ.toPrefunctor) f
      induction r <;> cat_disch)

Depends on / 依赖: FreeGroupoid, FreeGroupoid.homRel, Prefunctor, Prefunctor.congr_hom, Quiver, Quiver.FreeGroupoid.lift, Quiver.FreeGroupoid.lift_spec, Quotient, Quotient.lift, cat_disch, congr_hom, homRel, lift_spec, toPrefunctor
-/
def lift (φ : C ⥤ G) : FreeGroupoid C ⥤ G :=
  Quotient.lift (FreeGroupoid.homRel C) (Quiver.FreeGroupoid.lift φ.toPrefunctor)
    (fun _ _ f g r => by
      have {X Y : C} (f : X ⟶ Y) :=
        Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec φ.toPrefunctor) f
      induction r <;> cat_disch)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lift_spec` / 定理 `lift_spec`

English:
theorem lift_spec
  given: (φ : C ⥤ G)
  statement: of C ⋙ lift φ = φ
  proof: Functor.toPrefunctor_injective (by
    change Quiver.FreeGroupoid.of C ⋙q
      (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor ⋙q
        (lift φ).toPrefunctor = φ.toPrefunctor
    simp [lift, Quotient.lift_spec, Quiver.FreeGroupoid.lift_spec])

@[simp]

中文:
定理 lift_spec
  条件: (φ : C ⥤ G)
  结论: of C ⋙ lift φ = φ
  证明: Functor.toPrefunctor_injective (by
    change Quiver.FreeGroupoid.of C ⋙q
      (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor ⋙q
        (lift φ).toPrefunctor = φ.toPrefunctor
    simp [lift, Quotient.lift_spec, Quiver.FreeGroupoid.lift_spec])

@[simp]

Depends on / 依赖: FreeGroupoid, FreeGroupoid.homRel, Functor, Functor.toPrefunctor_injective, Quiver, Quiver.FreeGroupoid.lift_spec, Quiver.FreeGroupoid.of, Quotient, Quotient.functor, Quotient.lift_spec, functor, homRel, lift_spec, toPrefunctor, toPrefunctor_injective
-/
theorem lift_spec (φ : C ⥤ G) : of C ⋙ lift φ = φ :=
  Functor.toPrefunctor_injective (by
    change Quiver.FreeGroupoid.of C ⋙q
      (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor ⋙q
        (lift φ).toPrefunctor = φ.toPrefunctor
    simp [lift, Quotient.lift_spec, Quiver.FreeGroupoid.lift_spec])

@[simp]
/--
lemma `lift_obj_mk` / 引理 `lift_obj_mk`

English:
lemma lift_obj_mk
  given: {E : Type u₂} [Groupoid.{v₂} E] (φ : C ⥤ E) (X : C)
  proof: rfl

中文:
引理 lift_obj_mk
  条件: {E : 类型u₂} [群胚.{v₂} E] (φ : C ⥤ E) (X : C)
  证明: rfl
-/
lemma lift_obj_mk {E : Type u₂} [Groupoid.{v₂} E] (φ : C ⥤ E) (X : C) :
    (lift φ).obj (mk X) = φ.obj X := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `lift_map_homMk` / 引理 `lift_map_homMk`

English:
lemma lift_map_homMk
  given: {E : Type u₂} [Groupoid.{v₂} E] (φ : C ⥤ E) {X Y : C} (f : X ⟶ Y)
  proof: by
  simpa using Functor.congr_hom (lift_spec φ) f

中文:
引理 lift_map_homMk
  条件: {E : 类型u₂} [群胚.{v₂} E] (φ : C ⥤ E) {X Y : C} (f : X ⟶ Y)
  证明: by
  simpa using Functor.congr_hom (lift_spec φ) f

Depends on / 依赖: Functor, Functor.congr_hom, congr_hom, lift_spec
-/
lemma lift_map_homMk {E : Type u₂} [Groupoid.{v₂} E] (φ : C ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (lift φ).map (homMk f) = φ.map f := by
  simpa using Functor.congr_hom (lift_spec φ) f

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (φ : C ⥤ G) (Φ : FreeGroupoid C ⥤ G) (hΦ : of C ⋙ Φ = φ)
  proof: by
  apply Quotient.lift_unique
  apply Quiver.FreeGroupoid.lift_unique
  exact congr_arg Functor.toPrefunctor hΦ

中文:
定理 lift_unique
  条件: (φ : C ⥤ G) (Φ : FreeGroupoid C ⥤ G) (hΦ : of C ⋙ Φ = φ)
  证明: by
  apply Quotient.lift_unique
  apply Quiver.FreeGroupoid.lift_unique
  exact congr_arg Functor.toPrefunctor hΦ

Depends on / 依赖: FreeGroupoid, Functor, Functor.toPrefunctor, Quiver, Quiver.FreeGroupoid.lift_unique, Quotient, Quotient.lift_unique, congr_arg, lift_unique, toPrefunctor
-/
theorem lift_unique (φ : C ⥤ G) (Φ : FreeGroupoid C ⥤ G) (hΦ : of C ⋙ Φ = φ) :
    Φ = lift φ := by
  apply Quotient.lift_unique
  apply Quiver.FreeGroupoid.lift_unique
  exact congr_arg Functor.toPrefunctor hΦ

/--
theorem `lift_id_comp_of` / 定理 `lift_id_comp_of`

English:
theorem lift_id_comp_of
  statement: lift (𝟭 G) ⋙ of G = 𝟭 _
  proof: by
  rw [lift_unique (of G) (lift (𝟭 G) ⋙ of G) (by rw [← Functor.assoc]; rw [lift_spec]; rw [Functor.id_comp])]
  symm; apply lift_unique
  rw [Functor.comp_id]

中文:
定理 lift_id_comp_of
  结论: lift (𝟭 G) ⋙ of G = 𝟭 _
  证明: by
  rw [lift_unique (of G) (lift (𝟭 G) ⋙ of G) (by rw [← Functor.assoc]; rw [lift_spec]; rw [Functor.id_comp])]
  symm; apply lift_unique
  rw [Functor.comp_id]

Depends on / 依赖: Functor, Functor.assoc, Functor.comp_id, Functor.id_comp, comp_id, id_comp, lift_spec, lift_unique
-/
theorem lift_id_comp_of : lift (𝟭 G) ⋙ of G = 𝟭 _ := by
  rw [lift_unique (of G) (lift (𝟭 G) ⋙ of G) (by rw [← Functor.assoc]; rw [lift_spec]; rw [Functor.id_comp])]
  symm; apply lift_unique
  rw [Functor.comp_id]

/--
theorem `lift_comp` / 定理 `lift_comp`

English:
theorem lift_comp
  given: {H : Type u₂} [Groupoid.{v₂} H] (φ : C ⥤ G) (ψ : G ⥤ H)
  proof: by
  symm
  apply lift_unique
  rw [← Functor.assoc]; rw [lift_spec]

中文:
定理 lift_comp
  条件: {H : 类型u₂} [群胚.{v₂} H] (φ : C ⥤ G) (ψ : G ⥤ H)
  证明: by
  symm
  apply lift_unique
  rw [← Functor.assoc]; rw [lift_spec]

Depends on / 依赖: Functor, Functor.assoc, lift_spec, lift_unique
-/
theorem lift_comp {H : Type u₂} [Groupoid.{v₂} H] (φ : C ⥤ G) (ψ : G ⥤ H) :
    lift (φ ⋙ ψ) = lift φ ⋙ ψ := by
  symm
  apply lift_unique
  rw [← Functor.assoc]; rw [lift_spec]

/--
Definition of `strictUniversalPropertyFixedTarget` / `strictUniversalPropertyFixedTarget` 的定义

English:
definition strictUniversalPropertyFixedTarget
  signature: :
  body: inferInstance
  lift F _ := lift F
  fac _ _ := lift_spec ..
  uniq F G h := by rw [lift_unique (of C ⋙ G) F h, ← lift_unique (of C ⋙ G) G rfl]

中文:
定义 strictUniversalPropertyFixedTarget
  签名: :
  定义体: inferInstance
  lift F _ := lift F
  fac _ _ := lift_spec ..
  uniq F G h := by rw [lift_unique (of C ⋙ G) F h, ← lift_unique (of C ⋙ G) G rfl]
-/
def strictUniversalPropertyFixedTarget :
    Localization.StrictUniversalPropertyFixedTarget (of C) ⊤ G where
  inverts _ := inferInstance
  lift F _ := lift F
  fac _ _ := lift_spec ..
  uniq F G h := by rw [lift_unique (of C ⋙ G) F h, ← lift_unique (of C ⋙ G) G rfl]

attribute [local instance] Localization.groupoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (of C).IsLocalization ⊤
  body: .mk' _ _ strictUniversalPropertyFixedTarget strictUniversalPropertyFixedTarget

中文:
实例 :
  签名: (of C).是Localization ⊤
  定义体: .mk' _ _ strictUniversalPropertyFixedTarget strictUniversalPropertyFixedTarget

Depends on / 依赖: strictUniversalPropertyFixedTarget
-/
instance : (of C).IsLocalization ⊤ :=
  .mk' _ _ strictUniversalPropertyFixedTarget strictUniversalPropertyFixedTarget

/--
Definition of `liftNatIso` / `liftNatIso` 的定义

English:
definition liftNatIso
  signature: (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂)
  body: Localization.liftNatIso (of C) ⊤ (of C ⋙ F₁) (of C ⋙ F₂) _ _ τ

@[simp]

中文:
定义 lift自然数Iso
  签名: (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂)
  定义体: Localization.liftNatIso (of C) ⊤ (of C ⋙ F₁) (of C ⋙ F₂) _ _ τ

@[simp]

Depends on / 依赖: Localization, Localization.liftNatIso, liftNatIso
-/
def liftNatIso (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) : F₁ ≅ F₂ :=
  Localization.liftNatIso (of C) ⊤ (of C ⋙ F₁) (of C ⋙ F₂) _ _ τ

@[simp]
/--
lemma `liftNatIso_hom_app` / 引理 `liftNatIso_hom_app`

English:
lemma liftNatIso_hom_app
  given: (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X)
  proof: by
  simp [liftNatIso]

@[simp]

中文:
引理 lift自然数Iso_hom_app
  条件: (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X)
  证明: by
  simp [liftNatIso]

@[simp]

Depends on / 依赖: liftNatIso
-/
lemma liftNatIso_hom_app (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X) :
    (liftNatIso F₁ F₂ τ).hom.app (mk X) = τ.hom.app X := by
  simp [liftNatIso]

@[simp]
/--
lemma `liftNatIso_inv_app` / 引理 `liftNatIso_inv_app`

English:
lemma liftNatIso_inv_app
  given: (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X)
  proof: by
  simp [liftNatIso]

中文:
引理 lift自然数Iso_inv_app
  条件: (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X)
  证明: by
  simp [liftNatIso]

Depends on / 依赖: liftNatIso
-/
lemma liftNatIso_inv_app (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X) :
    (liftNatIso F₁ F₂ τ).inv.app (mk X) = τ.inv.app X := by
  simp [liftNatIso]

end UniversalProperty

section Functoriality

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (φ : C ⥤ D)
  body: lift (φ ⋙ of D)

中文:
定义 map
  签名: (φ : C ⥤ D)
  定义体: lift (φ ⋙ of D)
-/
def map (φ : C ⥤ D) : FreeGroupoid C ⥤ FreeGroupoid D :=
  lift (φ ⋙ of D)

/--
lemma `of_comp_map` / 引理 `of_comp_map`

English:
lemma of_comp_map
  given: (F : C ⥤ D)
  statement: of C ⋙ map F = F ⋙ of D
  proof: rfl

中文:
引理 of_comp_map
  条件: (F : C ⥤ D)
  结论: of C ⋙ map F = F ⋙ of D
  证明: rfl
-/
lemma of_comp_map (F : C ⥤ D) : of C ⋙ map F = F ⋙ of D := rfl

/--
Definition of `ofCompMapIso` / `ofCompMapIso` 的定义

English:
definition ofCompMapIso
  signature: (F : C ⥤ D)
  body: Iso.refl _

中文:
定义 ofCompMapIso
  签名: (F : C ⥤ D)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def ofCompMapIso (F : C ⥤ D) : of C ⋙ map F ≅ F ⋙ of D := Iso.refl _

variable (C) in
/--
Definition of `mapId` / `mapId` 的定义

English:
definition mapId
  signature: : map (𝟭 C) ≅ 𝟭 (FreeGroupoid C)
  body: liftNatIso _ _ (Iso.refl _)

@[simp]

中文:
定义 mapId
  签名: : map (𝟭 C) ≅ 𝟭 (FreeGroupoid C)
  定义体: liftNatIso _ _ (Iso.refl _)

@[simp]

Depends on / 依赖: Iso.refl, liftNatIso
-/
def mapId : map (𝟭 C) ≅ 𝟭 (FreeGroupoid C) :=
  liftNatIso _ _ (Iso.refl _)

@[simp]
/--
lemma `mapId_hom_app` / 引理 `mapId_hom_app`

English:
lemma mapId_hom_app
  given: (X)
  statement: (mapId C).hom.app X = 𝟙 X
  proof: liftNatIso_hom_app ..

@[simp]

中文:
引理 mapId_hom_app
  条件: (X)
  结论: (mapId C).hom.app X = 𝟙 X
  证明: liftNatIso_hom_app ..

@[simp]

Depends on / 依赖: liftNatIso_hom_app
-/
lemma mapId_hom_app (X) : (mapId C).hom.app X = 𝟙 X :=
  liftNatIso_hom_app ..

@[simp]
/--
lemma `mapId_inv_app` / 引理 `mapId_inv_app`

English:
lemma mapId_inv_app
  given: (X)
  statement: (mapId C).inv.app X = 𝟙 X
  proof: liftNatIso_inv_app ..

中文:
引理 mapId_inv_app
  条件: (X)
  结论: (mapId C).inv.app X = 𝟙 X
  证明: liftNatIso_inv_app ..

Depends on / 依赖: liftNatIso_inv_app
-/
lemma mapId_inv_app (X) : (mapId C).inv.app X = 𝟙 X :=
  liftNatIso_inv_app ..

variable (C) in
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (𝟭 C) = 𝟭 (FreeGroupoid C)
  proof: by
  symm; apply lift_unique; rfl

中文:
定理 map_id
  结论: map (𝟭 C) = 𝟭 (FreeGroupoid C)
  证明: by
  symm; apply lift_unique; rfl

Depends on / 依赖: lift_unique
-/
theorem map_id : map (𝟭 C) = 𝟭 (FreeGroupoid C) := by
  symm; apply lift_unique; rfl

/--
Definition of `mapComp` / `mapComp` 的定义

English:
definition mapComp
  signature: (φ : C ⥤ D) (φ' : D ⥤ E)
  body: liftNatIso _ _ (Iso.refl _)

@[simp]

中文:
定义 mapComp
  签名: (φ : C ⥤ D) (φ' : D ⥤ E)
  定义体: liftNatIso _ _ (Iso.refl _)

@[simp]

Depends on / 依赖: Iso.refl, liftNatIso
-/
def mapComp (φ : C ⥤ D) (φ' : D ⥤ E) : map (φ ⋙ φ') ≅ map φ ⋙ map φ' :=
  liftNatIso _ _ (Iso.refl _)

@[simp]
/--
lemma `mapComp_hom_app` / 引理 `mapComp_hom_app`

English:
lemma mapComp_hom_app
  given: (φ : C ⥤ D) (φ' : D ⥤ E) (X)
  statement: (mapComp φ φ').hom.app X = 𝟙 _
  proof: liftNatIso_hom_app ..

@[simp]

中文:
引理 mapComp_hom_app
  条件: (φ : C ⥤ D) (φ' : D ⥤ E) (X)
  结论: (mapComp φ φ').hom.app X = 𝟙 _
  证明: liftNatIso_hom_app ..

@[simp]

Depends on / 依赖: liftNatIso_hom_app
-/
lemma mapComp_hom_app (φ : C ⥤ D) (φ' : D ⥤ E) (X) : (mapComp φ φ').hom.app X = 𝟙 _ :=
  liftNatIso_hom_app ..

@[simp]
/--
lemma `mapComp_inv_app` / 引理 `mapComp_inv_app`

English:
lemma mapComp_inv_app
  given: (φ : C ⥤ D) (φ' : D ⥤ E) (X)
  statement: (mapComp φ φ').inv.app X = 𝟙 _
  proof: liftNatIso_inv_app ..

中文:
引理 mapComp_inv_app
  条件: (φ : C ⥤ D) (φ' : D ⥤ E) (X)
  结论: (mapComp φ φ').inv.app X = 𝟙 _
  证明: liftNatIso_inv_app ..

Depends on / 依赖: liftNatIso_inv_app
-/
lemma mapComp_inv_app (φ : C ⥤ D) (φ' : D ⥤ E) (X) : (mapComp φ φ').inv.app X = 𝟙 _ :=
  liftNatIso_inv_app ..

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (φ : C ⥤ D) (φ' : D ⥤ E)
  statement: map (φ ⋙ φ') = map φ ⋙ map φ'
  proof: by
  symm; apply lift_unique; rfl

@[simp]

中文:
定理 map_comp
  条件: (φ : C ⥤ D) (φ' : D ⥤ E)
  结论: map (φ ⋙ φ') = map φ ⋙ map φ'
  证明: by
  symm; apply lift_unique; rfl

@[simp]

Depends on / 依赖: lift_unique
-/
theorem map_comp (φ : C ⥤ D) (φ' : D ⥤ E) : map (φ ⋙ φ') = map φ ⋙ map φ' := by
  symm; apply lift_unique; rfl

@[simp]
/--
lemma `map_obj_mk` / 引理 `map_obj_mk`

English:
lemma map_obj_mk
  given: (φ : C ⥤ D) (X : C)
  statement: (map φ).obj (mk X) = mk (φ.obj X)
  proof: rfl

@[simp]

中文:
引理 map_obj_mk
  条件: (φ : C ⥤ D) (X : C)
  结论: (map φ).obj (mk X) = mk (φ.obj X)
  证明: rfl

@[simp]
-/
lemma map_obj_mk (φ : C ⥤ D) (X : C) : (map φ).obj (mk X) = mk (φ.obj X) := rfl

@[simp]
/--
lemma `map_map_homMk` / 引理 `map_map_homMk`

English:
lemma map_map_homMk
  given: (φ : C ⥤ D) {X Y : C} (f : X ⟶ Y)
  proof: rfl

中文:
引理 map_map_homMk
  条件: (φ : C ⥤ D) {X Y : C} (f : X ⟶ Y)
  证明: rfl
-/
lemma map_map_homMk (φ : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    (map φ).map (homMk f) = homMk (φ.map f) := rfl

variable {E : Type u₂} [Groupoid.{v₂} E]

/--
lemma `map_comp_lift` / 引理 `map_comp_lift`

English:
lemma map_comp_lift
  given: (F : C ⥤ D) (G : D ⥤ E)
  statement: map F ⋙ lift G = lift (F ⋙ G)
  proof: by
  apply lift_unique
  rw [← Functor.assoc]; rw [of_comp_map]; rw [Functor.assoc]; rw [lift_spec G]

中文:
引理 map_comp_lift
  条件: (F : C ⥤ D) (G : D ⥤ E)
  结论: map F ⋙ lift G = lift (F ⋙ G)
  证明: by
  apply lift_unique
  rw [← Functor.assoc]; rw [of_comp_map]; rw [Functor.assoc]; rw [lift_spec G]

Depends on / 依赖: Functor, Functor.assoc, lift_spec, lift_unique, of_comp_map
-/
lemma map_comp_lift (F : C ⥤ D) (G : D ⥤ E) : map F ⋙ lift G = lift (F ⋙ G) := by
  apply lift_unique
  rw [← Functor.assoc]; rw [of_comp_map]; rw [Functor.assoc]; rw [lift_spec G]

/--
Definition of `mapCompLift` / `mapCompLift` 的定义

English:
definition mapCompLift
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: liftNatIso _ _ (Iso.refl _)

@[simp]

中文:
定义 mapCompLift
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: liftNatIso _ _ (Iso.refl _)

@[simp]

Depends on / 依赖: Iso.refl, liftNatIso
-/
def mapCompLift (F : C ⥤ D) (G : D ⥤ E) : map F ⋙ lift G ≅ lift (F ⋙ G) :=
  liftNatIso _ _ (Iso.refl _)

@[simp]
/--
lemma `mapCompLift_hom_app` / 引理 `mapCompLift_hom_app`

English:
lemma mapCompLift_hom_app
  given: (F : C ⥤ D) (G : D ⥤ E) (X)
  statement: (mapCompLift F G).hom.app X = 𝟙 _
  proof: liftNatIso_hom_app ..

@[simp]

中文:
引理 mapCompLift_hom_app
  条件: (F : C ⥤ D) (G : D ⥤ E) (X)
  结论: (mapCompLift F G).hom.app X = 𝟙 _
  证明: liftNatIso_hom_app ..

@[simp]

Depends on / 依赖: liftNatIso_hom_app
-/
lemma mapCompLift_hom_app (F : C ⥤ D) (G : D ⥤ E) (X) : (mapCompLift F G).hom.app X = 𝟙 _ :=
  liftNatIso_hom_app ..

@[simp]
/--
lemma `mapCompLift_inv_app` / 引理 `mapCompLift_inv_app`

English:
lemma mapCompLift_inv_app
  given: (F : C ⥤ D) (G : D ⥤ E) (X)
  statement: (mapCompLift F G).inv.app X = 𝟙 _
  proof: liftNatIso_inv_app ..

中文:
引理 mapCompLift_inv_app
  条件: (F : C ⥤ D) (G : D ⥤ E) (X)
  结论: (mapCompLift F G).inv.app X = 𝟙 _
  证明: liftNatIso_inv_app ..

Depends on / 依赖: liftNatIso_inv_app
-/
lemma mapCompLift_inv_app (F : C ⥤ D) (G : D ⥤ E) (X) : (mapCompLift F G).inv.app X = 𝟙 _ :=
  liftNatIso_inv_app ..

end Functoriality

/-- Functors out of the free groupoid biject with functors out of the original category. -/
@[simps]
/--
Definition of `functorEquiv` / `functorEquiv` 的定义

English:
definition functorEquiv
  signature: {D : Type*} [Groupoid D]
  body: of C ⋙ G
  invFun F := lift F
  right_inv := lift_spec
  left_inv _ := (lift_unique _ _ rfl).symm

中文:
定义 functorEquiv
  签名: {D : 类型} [群胚 D]
  定义体: of C ⋙ G
  invFun F := lift F
  right_inv := lift_spec
  left_inv _ := (lift_unique _ _ rfl).symm
-/
def functorEquiv {D : Type*} [Groupoid D] : (FreeGroupoid C ⥤ D) ≃ (C ⥤ D) where
  toFun G := of C ⋙ G
  invFun F := lift F
  right_inv := lift_spec
  left_inv _ := (lift_unique _ _ rfl).symm

end FreeGroupoid

namespace Grpd

open FreeGroupoid

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: : Cat.{u, u} ⥤ Grpd.{u, u} where
  body: Grpd.of FreeGroupoid C
  map {C D} F := map F.toFunctor
  map_id C := by simp [map_id, id_eq_id]
  map_comp F G := by simp [Grpd.comp_eq_comp, map_comp]

@[simp]

中文:
定义 free
  签名: : Cat.{u, u} ⥤ Grpd.{u, u} where
  定义体: Grpd.of FreeGroupoid C
  map {C D} F := map F.toFunctor
  map_id C := by simp [map_id, id_eq_id]
  map_comp F G := by simp [Grpd.comp_eq_comp, map_comp]

@[simp]

Depends on / 依赖: FreeGroupoid, Grpd.of
-/
def free : Cat.{u, u} ⥤ Grpd.{u, u} where
obj C := Grpd.of FreeGroupoid C
  map {C D} F := map F.toFunctor
  map_id C := by simp [map_id, id_eq_id]
  map_comp F G := by simp [Grpd.comp_eq_comp, map_comp]

@[simp]
/--
lemma `free_obj` / 引理 `free_obj`

English:
lemma free_obj
  given: (C : Cat.{u, u})
  statement: free.obj C = FreeGroupoid C
  proof: rfl

@[simp]

中文:
引理 free_obj
  条件: (C : Cat.{u, u})
  结论: free.obj C = FreeGroupoid C
  证明: rfl

@[simp]
-/
lemma free_obj (C : Cat.{u, u}) : free.obj C = FreeGroupoid C :=
  rfl

@[simp]
/--
lemma `free_map` / 引理 `free_map`

English:
lemma free_map
  given: {C D : Cat.{u, u}} (F : C ⟶ D)
  statement: free.map F = map F.toFunctor
  proof: rfl

中文:
引理 free_map
  条件: {C D : Cat.{u, u}} (F : C ⟶ D)
  结论: free.map F = map F.toFunctor
  证明: rfl
-/
lemma free_map {C D : Cat.{u, u}} (F : C ⟶ D) : free.map F = map F.toFunctor :=
  rfl

/--
Definition of `freeForgetAdjunction` / `freeForgetAdjunction` 的定义

English:
definition freeForgetAdjunction
  signature: : free ⊣ Grpd.forgetToCat
  body: Adjunction.mkOfHomEquiv
    { homEquiv _ _ := FreeGroupoid.functorEquiv.trans (Functor.equivCatHom _ _)
      homEquiv_naturality_left_symm _ _ := (FreeGroupoid.map_comp_lift _ _).symm
      homEquiv_naturality_right _ _ := rfl }

中文:
定义 freeForgetAdjunction
  签名: : free ⊣ Grpd.forgetToCat
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv _ _ := FreeGroupoid.functorEquiv.trans (Functor.equivCatHom _ _)
      homEquiv_naturality_left_symm _ _ := (FreeGroupoid.map_comp_lift _ _).symm
      homEquiv_naturality_right _ _ := rfl }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, FreeGroupoid, FreeGroupoid.functorEquiv.trans, FreeGroupoid.map_comp_lift, Functor, Functor.equivCatHom, equivCatHom, functorEquiv, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, map_comp_lift, mkOfHomEquiv
-/
def freeForgetAdjunction : free ⊣ Grpd.forgetToCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := FreeGroupoid.functorEquiv.trans (Functor.equivCatHom _ _)
      homEquiv_naturality_left_symm _ _ := (FreeGroupoid.map_comp_lift _ _).symm
      homEquiv_naturality_right _ _ := rfl }

variable {C : Type u} [Category.{u} C] {D : Type u} [Groupoid.{u} D]

@[simp]
/--
lemma `freeForgetAdjunction_homEquiv_apply` / 引理 `freeForgetAdjunction_homEquiv_apply`

English:
lemma freeForgetAdjunction_homEquiv_apply
  given: (F : FreeGroupoid C ⥤ D)
  proof: rfl

@[simp]

中文:
引理 freeForgetAdjunction_homEquiv_apply
  条件: (F : FreeGroupoid C ⥤ D)
  证明: rfl

@[simp]
-/
lemma freeForgetAdjunction_homEquiv_apply (F : FreeGroupoid C ⥤ D) :
    (freeForgetAdjunction.homEquiv (Cat.of C) (Grpd.of D) F).toFunctor = FreeGroupoid.of C ⋙ F :=
  rfl

@[simp]
/--
lemma `freeForgetAdjunction_homEquiv_symm_apply` / 引理 `freeForgetAdjunction_homEquiv_symm_apply`

English:
lemma freeForgetAdjunction_homEquiv_symm_apply
  given: (F : C ⥤ D)
  proof: rfl

@[simp]

中文:
引理 freeForgetAdjunction_homEquiv_symm_apply
  条件: (F : C ⥤ D)
  证明: rfl

@[simp]
-/
lemma freeForgetAdjunction_homEquiv_symm_apply (F : C ⥤ D) :
    (freeForgetAdjunction.homEquiv (Cat.of C) (Grpd.of D)).symm F.toCatHom = map F ⋙ lift (𝟭 D) :=
  rfl

@[simp]
/--
lemma `freeForgetAdjunction_unit_app` / 引理 `freeForgetAdjunction_unit_app`

English:
lemma freeForgetAdjunction_unit_app
  proof: rfl

@[simp]

中文:
引理 freeForgetAdjunction_unit_app
  证明: rfl

@[simp]
-/
lemma freeForgetAdjunction_unit_app :
    (freeForgetAdjunction.unit.app (Cat.of C)).toFunctor = FreeGroupoid.of C :=
  rfl

@[simp]
/--
lemma `freeForgetAdjunction_counit_app` / 引理 `freeForgetAdjunction_counit_app`

English:
lemma freeForgetAdjunction_counit_app
  proof: rfl

中文:
引理 freeForgetAdjunction_counit_app
  证明: rfl
-/
lemma freeForgetAdjunction_counit_app :
    freeForgetAdjunction.counit.app (Grpd.of D) = lift (𝟭 D) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Reflective Grpd.forgetToCat
  body: free
  adj := freeForgetAdjunction

中文:
实例 :
  签名: 反射 Grpd.forgetToCat
  定义体: free
  adj := freeForgetAdjunction
-/
instance : Reflective Grpd.forgetToCat where
  L := free
  adj := freeForgetAdjunction

end Grpd
end CategoryTheory
end
