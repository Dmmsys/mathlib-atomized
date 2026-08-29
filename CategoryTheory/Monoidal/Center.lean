/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Half braidings and the Drinfeld center of a monoidal category

We define `Center C` to be pairs `⟨X, b⟩`, where `X : C` and `b` is a half-braiding on `X`.

We show that `Center C` is braided monoidal,
and provide the monoidal functor `Center.forget` from `Center C` back to `C`.

## Implementation notes

Verifying the various axioms directly requires tedious rewriting.
Using the `slice` tactic may make the proofs marginally more readable.

More exciting, however, would be to make possible one of the following options:
1. Integration with homotopy.io / globular to give "picture proofs".
2. The monoidal coherence theorem, so we can ignore associators
   (after which most of these proofs are trivial).
3. Automating these proofs using `rewrite_search` or some relative.

In this file, we take the second approach using the monoidal composition `⊗≫` and the
`coherence` tactic.
-/

@[expose] public section


universe v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/--
Definition of `HalfBraiding` / `HalfBraiding` 的定义

English:
structure HalfBraiding
  parameters: (X : C)
  axioms and operations (3):
    - β : forall U, X otimes U ≅ U otimes X
    - monoidal : forall U U', (β (U otimes U')).hom = (α_ _ _ _).inv ≫ ((β U).hom ▷ U') ≫ (α_ _ _ _).hom ≫ (U ◁ (β U').hom) ≫ (α_ _ _ _).inv  [default: by cat_disch]
    - naturality : forall {U U'} (f : U ⟶ U'), (X ◁ f) ≫ (β U').hom = (β U).hom ≫ (f ▷ X)  [default: by cat_disch]

中文:
结构 HalfBraiding
  参数: (X : C)
  公理与运算 (3 个):
    - β : 对任意 U, X otimes U ≅ U otimes X
    - monoidal : 对任意 U U', (β (U otimes U')).hom = (α_ _ _ _).inv ≫ ((β U).hom ▷ U') ≫ (α_ _ _ _).hom ≫ (U ◁ (β U').hom) ≫ (α_ _ _ _).inv  [默认: by cat_disch]
    - naturality : 对任意 {U U'} (f : U ⟶ U'), (X ◁ f) ≫ (β U').hom = (β U).hom ≫ (f ▷ X)  [默认: by cat_disch]

Depends on / 依赖: cat_disch, naturality
-/
structure HalfBraiding (X : C) where
  /-- The family of isomorphisms `X ⊗ U ≅ U ⊗ X` -/
  β : forall U, X otimes U ≅ U otimes X
  monoidal : forall U U', (β (U otimes U')).hom =
      (α_ _ _ _).inv ≫
        ((β U).hom ▷ U') ≫ (α_ _ _ _).hom ≫ (U ◁ (β U').hom) ≫ (α_ _ _ _).inv := by
    cat_disch
  naturality : forall {U U'} (f : U ⟶ U'), (X ◁ f) ≫ (β U').hom = (β U).hom ≫ (f ▷ X) := by
    cat_disch

attribute [reassoc, simp] HalfBraiding.monoidal -- the reassoc lemma is redundant as a simp lemma

attribute [simp, reassoc] HalfBraiding.naturality

variable (C)

/--
Definition of `Center` / `Center` 的定义

English:
definition Center
  body: Σ X : C, HalfBraiding X

中文:
定义 中心
  定义体: Σ X : C, HalfBraiding X

Depends on / 依赖: HalfBraiding
-/
def Center :=
  Σ X : C, HalfBraiding X

namespace Center

variable {C}

/-- A morphism in the Drinfeld center of `C`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : Center C)
  axioms and operations (2):
    - f : X.1 ⟶ Y.1
    - comm : forall U, (f ▷ U) ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ (U ◁ f)  [default: by cat_disch]

中文:
结构 态射
  参数: (X Y : 中心 C)
  公理与运算 (2 个):
    - f : X.1 ⟶ Y.1
    - comm : 对任意 U, (f ▷ U) ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ (U ◁ f)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (X Y : Center C) where
  /-- The underlying morphism between the first components of the objects involved -/
  f : X.1 ⟶ Y.1
  comm : forall U, (f ▷ U) ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ (U ◁ f) := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Quiver (Center C)
  body: Hom

@[ext]

中文:
实例 :
  签名: 箭图 (中心 C)
  定义体: Hom

@[ext]
-/
instance : Quiver (Center C) where
  Hom := Hom

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {X Y : Center C} (f g : X ⟶ Y) (w : f.f = g.f)
  statement: f = g
  proof: by
  cases f; cases g; congr

中文:
定理 ext
  条件: {X Y : 中心 C} (f g : X ⟶ Y) (w : f.f = g.f)
  结论: f = g
  证明: by
  cases f; cases g; congr
-/
theorem ext {X Y : Center C} (f g : X ⟶ Y) (w : f.f = g.f) : f = g := by
  cases f; cases g; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Center C)
  body: { f := 𝟙 X.1 }
  comp f g := { f := f.f ≫ g.f }

@[simp]

中文:
实例 :
  签名: 范畴 (中心 C)
  定义体: { f := 𝟙 X.1 }
  comp f g := { f := f.f ≫ g.f }

@[simp]
-/
instance : Category (Center C) where
  id X := { f := 𝟙 X.1 }
  comp f g := { f := f.f ≫ g.f }

@[simp]
/--
theorem `id_f` / 定理 `id_f`

English:
theorem id_f
  given: (X : Center C)
  statement: Hom.f (𝟙 X) = 𝟙 X.1
  proof: rfl

@[simp]

中文:
定理 id_f
  条件: (X : 中心 C)
  结论: 态射.f (𝟙 X) = 𝟙 X.1
  证明: rfl

@[simp]
-/
theorem id_f (X : Center C) : Hom.f (𝟙 X) = 𝟙 X.1 :=
  rfl

@[simp]
/--
theorem `comp_f` / 定理 `comp_f`

English:
theorem comp_f
  given: {X Y Z : Center C} (f : X ⟶ Y) (g : Y ⟶ Z)
  statement: (f ≫ g).f = f.f ≫ g.f
  proof: rfl

中文:
定理 comp_f
  条件: {X Y Z : 中心 C} (f : X ⟶ Y) (g : Y ⟶ Z)
  结论: (f ≫ g).f = f.f ≫ g.f
  证明: rfl
-/
theorem comp_f {X Y Z : Center C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f :=
  rfl

/-- Construct an isomorphism in the Drinfeld center from
a morphism whose underlying morphism is an isomorphism.
-/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {X Y : Center C} (f : X ⟶ Y) [IsIso f.f]
  body: f
  inv := ⟨inv f.f,
    fun U => by simp [← cancel_epi (f.f ▷ U), ← comp_whiskerRight_assoc,
      ← MonoidalCategory.whiskerLeft_comp] ⟩

中文:
定义 isoMk
  签名: {X Y : 中心 C} (f : X ⟶ Y) [是同构 f.f]
  定义体: f
  inv := ⟨inv f.f,
    fun U => by simp [← cancel_epi (f.f ▷ U), ← comp_whiskerRight_assoc,
      ← MonoidalCategory.whiskerLeft_comp] ⟩
-/
def isoMk {X Y : Center C} (f : X ⟶ Y) [IsIso f.f] : X ≅ Y where
  hom := f
  inv := ⟨inv f.f,
    fun U => by simp [← cancel_epi (f.f ▷ U), ← comp_whiskerRight_assoc,
      ← MonoidalCategory.whiskerLeft_comp] ⟩

/--
Instance `isIso_of_f_isIso` / 实例 `isIso_of_f_isIso`

English:
instance isIso_of_f_isIso
  signature: {X Y : Center C} (f : X ⟶ Y) [IsIso f.f]
  body: by
  change IsIso (isoMk f).hom
  infer_instance

中文:
实例 isIso_of_f_isIso
  签名: {X Y : 中心 C} (f : X ⟶ Y) [是同构 f.f]
  定义体: by
  change IsIso (isoMk f).hom
  infer_instance

Depends on / 依赖: infer_instance
-/
instance isIso_of_f_isIso {X Y : Center C} (f : X ⟶ Y) [IsIso f.f] : IsIso f := by
  change IsIso (isoMk f).hom
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
@[simps]
/--
Definition of `tensorObj` / `tensorObj` 的定义

English:
definition tensorObj
  signature: (X Y : Center C)
  body: ⟨X.1 otimes Y.1,
    { β := fun U =>
        α_ _ _ _ ≪≫
          (whiskerLeftIso X.1 (Y.2.β U)) ≪≫ (α_ _ _ _).symm ≪≫
            (whiskerRightIso (X.2.β U) Y.1) ≪≫ α_ _ _ _
      monoidal := fun U U' => by
        dsimp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
 

中文:
定义 tensorObj
  签名: (X Y : 中心 C)
  定义体: ⟨X.1 otimes Y.1,
    { β := fun U =>
        α_ _ _ _ ≪≫
          (whiskerLeftIso X.1 (Y.2.β U)) ≪≫ (α_ _ _ _).symm ≪≫
            (whiskerRightIso (X.2.β U) Y.1) ≪≫ α_ _ _ _
      monoidal := fun U U' => by
        dsimp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
 

Depends on / 依赖: HalfBraiding, HalfBraiding.monoidal, Iso.symm_hom, Iso.trans_hom, monoidal, otimes, symm_hom, trans_hom, whiskerLeftIso, whiskerLeftIso_hom, whiskerRightIso, whiskerRightIso_hom
-/
def tensorObj (X Y : Center C) : Center C :=
  ⟨X.1 otimes Y.1,
    { β := fun U =>
        α_ _ _ _ ≪≫
          (whiskerLeftIso X.1 (Y.2.β U)) ≪≫ (α_ _ _ _).symm ≪≫
            (whiskerRightIso (X.2.β U) Y.1) ≪≫ α_ _ _ _
      monoidal := fun U U' => by
        dsimp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
        simp only [HalfBraiding.monoidal]
        -- We'd like to commute `X.1 ◁ U ◁ (HalfBraiding.β Y.2 U').hom`
        -- and `((HalfBraiding.β X.2 U).hom ▷ U' ▷ Y.1)` past each other.
        -- We do this with the help of the monoidal composition `⊗≫` and the `coherence` tactic.
        calc
          _ = 𝟙 _ otimes≫
            X.1 ◁ (HalfBraiding.β Y.2 U).hom ▷ U' otimes≫
              (_ ◁ (HalfBraiding.β Y.2 U').hom ≫
                (HalfBraiding.β X.2 U).hom ▷ _) otimes≫
                  U ◁ (HalfBraiding.β X.2 U').hom ▷ Y.1 otimes≫ 𝟙 _ := by monoidal
          _ = _ := by rw [whisker_exchange]; monoidal
      naturality := fun {U U'} f => by
        dsimp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
        calc
          _ = 𝟙 _ otimes≫
            (X.1 ◁ (Y.1 ◁ f ≫ (HalfBraiding.β Y.2 U').hom)) otimes≫
              (HalfBraiding.β X.2 U').hom ▷ Y.1 otimes≫ 𝟙 _ := by monoidal
          _ = 𝟙 _ otimes≫
            X.1 ◁ (HalfBraiding.β Y.2 U).hom otimes≫
              (X.1 ◁ f ≫ (HalfBraiding.β X.2 U').hom) ▷ Y.1 otimes≫ 𝟙 _ := by
            rw [HalfBraiding.naturality]; monoidal
          _ = _ := by rw [HalfBraiding.naturality]; monoidal }⟩

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
theorem `whiskerLeft_comm` / 定理 `whiskerLeft_comm`

English:
theorem whiskerLeft_comm
  given: (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) (U : C)
  proof: by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ otimes≫
      X.fst ◁ (f.f ▷ U ≫ (HalfBraiding.β Y₂.snd U).hom) otimes≫
        (HalfBraiding.β X.snd U).hom ▷ Y₂.fst otimes≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ o

中文:
定理 whiskerLeft_comm
  条件: (X : 中心 C) {Y₁ Y₂ : 中心 C} (f : Y₁ ⟶ Y₂) (U : C)
  证明: by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ otimes≫
      X.fst ◁ (f.f ▷ U ≫ (HalfBraiding.β Y₂.snd U).hom) otimes≫
        (HalfBraiding.β X.snd U).hom ▷ Y₂.fst otimes≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ o

Depends on / 依赖: HalfBraiding, Iso.symm_hom, Iso.trans_hom, X.fst, X.snd, f.comm, monoidal, otimes, symm_hom, tensorObj_fst, trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom, whisker_exchange
-/
theorem whiskerLeft_comm (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) (U : C) :
    (X.1 ◁ f.f) ▷ U ≫ ((tensorObj X Y₂).2.β U).hom =
      ((tensorObj X Y₁).2.β U).hom ≫ U ◁ X.1 ◁ f.f := by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ otimes≫
      X.fst ◁ (f.f ▷ U ≫ (HalfBraiding.β Y₂.snd U).hom) otimes≫
        (HalfBraiding.β X.snd U).hom ▷ Y₂.fst otimes≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ otimes≫
      X.fst ◁ (HalfBraiding.β Y₁.snd U).hom otimes≫
        ((X.fst otimes U) ◁ f.f ≫ (HalfBraiding.β X.snd U).hom ▷ Y₂.fst) otimes≫ 𝟙 _ := by
      rw [f.comm]; monoidal
    _ = _ := by rw [whisker_exchange]; monoidal

/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
definition whiskerLeft
  signature: (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂)
  body: X.1 ◁ f.f
  comm U := whiskerLeft_comm X f U

中文:
定义 whiskerLeft
  签名: (X : 中心 C) {Y₁ Y₂ : 中心 C} (f : Y₁ ⟶ Y₂)
  定义体: X.1 ◁ f.f
  comm U := whiskerLeft_comm X f U
-/
def whiskerLeft (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) :
    tensorObj X Y₁ ⟶ tensorObj X Y₂ where
  f := X.1 ◁ f.f
  comm U := whiskerLeft_comm X f U

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in -- Needed below.
@[reassoc]
/--
theorem `whiskerRight_comm` / 定理 `whiskerRight_comm`

English:
theorem whiskerRight_comm
  given: {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) (U : C)
  proof: by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ otimes≫
      (f.f ▷ (Y.fst otimes U) ≫ X₂.fst ◁ (HalfBraiding.β Y.snd U).hom) otimes≫
        (HalfBraiding.β X₂.snd U).hom ▷ Y.fst otimes≫ 𝟙 _ := by monoida

中文:
定理 whiskerRight_comm
  条件: {X₁ X₂ : 中心 C} (f : X₁ ⟶ X₂) (Y : 中心 C) (U : C)
  证明: by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ otimes≫
      (f.f ▷ (Y.fst otimes U) ≫ X₂.fst ◁ (HalfBraiding.β Y.snd U).hom) otimes≫
        (HalfBraiding.β X₂.snd U).hom ▷ Y.fst otimes≫ 𝟙 _ := by monoida

Depends on / 依赖: HalfBraiding, Iso.symm_hom, Iso.trans_hom, Y.fst, Y.snd, f.comm, monoidal, otimes, symm_hom, tensorObj_fst, trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom, whisker_exchange
-/
theorem whiskerRight_comm {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) (U : C) :
    f.f ▷ Y.1 ▷ U ≫ ((tensorObj X₂ Y).2.β U).hom =
      ((tensorObj X₁ Y).2.β U).hom ≫ U ◁ f.f ▷ Y.1 := by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ otimes≫
      (f.f ▷ (Y.fst otimes U) ≫ X₂.fst ◁ (HalfBraiding.β Y.snd U).hom) otimes≫
        (HalfBraiding.β X₂.snd U).hom ▷ Y.fst otimes≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ otimes≫
      X₁.fst ◁ (HalfBraiding.β Y.snd U).hom otimes≫
        (f.f ▷ U ≫ (HalfBraiding.β X₂.snd U).hom) ▷ Y.fst otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by rw [f.comm]; monoidal

/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
definition whiskerRight
  signature: {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C)
  body: f.f ▷ Y.1
  comm U := whiskerRight_comm f Y U

中文:
定义 whiskerRight
  签名: {X₁ X₂ : 中心 C} (f : X₁ ⟶ X₂) (Y : 中心 C)
  定义体: f.f ▷ Y.1
  comm U := whiskerRight_comm f Y U
-/
def whiskerRight {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) :
    tensorObj X₁ Y ⟶ tensorObj X₂ Y where
  f := f.f ▷ Y.1
  comm U := whiskerRight_comm f Y U

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
@[simps]
/--
Definition of `tensorHom` / `tensorHom` 的定义

English:
definition tensorHom
  signature: {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  body: f.f otimesₘ g.f
  comm U := by
    rw [tensorHom_def]; rw [comp_whiskerRight_assoc]; rw [whiskerLeft_comm]; rw [whiskerRight_comm_assoc]; rw [MonoidalCategory.whiskerLeft_comp]

中文:
定义 tensorHom
  签名: {X₁ Y₁ X₂ Y₂ : 中心 C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  定义体: f.f otimesₘ g.f
  comm U := by
    rw [tensorHom_def]; rw [comp_whiskerRight_assoc]; rw [whiskerLeft_comm]; rw [whiskerRight_comm_assoc]; rw [MonoidalCategory.whiskerLeft_comp]
-/
def tensorHom {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ where
  f := f.f otimesₘ g.f
  comm U := by
    rw [tensorHom_def]; rw [comp_whiskerRight_assoc]; rw [whiskerLeft_comm]; rw [whiskerRight_comm_assoc]; rw [MonoidalCategory.whiskerLeft_comp]

section

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
@[simps]
/--
Definition of `tensorUnit` / `tensorUnit` 的定义

English:
definition tensorUnit
  signature: : Center C
  body: ⟨𝟙_ C, { β := fun U => fun_ U ≪≫ (ρ_ U).symm }⟩

中文:
定义 tensorUnit
  签名: : 中心 C
  定义体: ⟨𝟙_ C, { β := fun U => fun_ U ≪≫ (ρ_ U).symm }⟩

Depends on / 依赖: fun_
-/
def tensorUnit : Center C :=
  ⟨𝟙_ C, { β := fun U => fun_ U ≪≫ (ρ_ U).symm }⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: (X Y Z : Center C)
  body: isoMk ⟨(α_ X.1 Y.1 Z.1).hom, fun U => by simp⟩

中文:
定义 associator
  签名: (X Y Z : 中心 C)
  定义体: isoMk ⟨(α_ X.1 Y.1 Z.1).hom, fun U => by simp⟩
-/
def associator (X Y Z : Center C) : tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  isoMk ⟨(α_ X.1 Y.1 Z.1).hom, fun U => by simp⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: (X : Center C)
  body: isoMk ⟨(fun_ X.1).hom, fun U => by simp⟩

中文:
定义 leftUnitor
  签名: (X : 中心 C)
  定义体: isoMk ⟨(fun_ X.1).hom, fun U => by simp⟩

Depends on / 依赖: fun_
-/
def leftUnitor (X : Center C) : tensorObj tensorUnit X ≅ X :=
  isoMk ⟨(fun_ X.1).hom, fun U => by simp⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: (X : Center C)
  body: isoMk ⟨(ρ_ X.1).hom, fun U => by simp⟩

中文:
定义 rightUnitor
  签名: (X : 中心 C)
  定义体: isoMk ⟨(ρ_ X.1).hom, fun U => by simp⟩
-/
def rightUnitor (X : Center C) : tensorObj X tensorUnit ≅ X :=
  isoMk ⟨(ρ_ X.1).hom, fun U => by simp⟩

end

section

attribute [local simp] associator_naturality leftUnitor_naturality rightUnitor_naturality pentagon

attribute [local simp] Center.associator Center.leftUnitor Center.rightUnitor

attribute [local simp] Center.whiskerLeft Center.whiskerRight Center.tensorHom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategory (Center C)
  body: tensorObj X Y
  tensorHom f g := tensorHom f g
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  whiskerLeft X _ _ f := whiskerLeft X f
  whiskerRight f Y := whiskerRight f Y
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

中文:
实例 :
  签名: 幺半群范畴 (中心 C)
  定义体: tensorObj X Y
  tensorHom f g := tensorHom f g
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  whiskerLeft X _ _ f := whiskerLeft X f
  whiskerRight f Y := whiskerRight f Y
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

Depends on / 依赖: tensorObj
-/
instance : MonoidalCategory (Center C) where
  tensorObj X Y := tensorObj X Y
  tensorHom f g := tensorHom f g
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  whiskerLeft X _ _ f := whiskerLeft X f
  whiskerRight f Y := whiskerRight f Y
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `tensor_fst` / 定理 `tensor_fst`

English:
theorem tensor_fst
  given: (X Y : Center C)
  statement: (X otimes Y).1 = X.1 otimes Y.1
  proof: rfl

中文:
定理 tensor_fst
  条件: (X Y : 中心 C)
  结论: (X otimes Y).1 = X.1 otimes Y.1
  证明: rfl
-/
theorem tensor_fst (X Y : Center C) : (X otimes Y).1 = X.1 otimes Y.1 :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `tensor_β` / 定理 `tensor_β`

English:
theorem tensor_β
  given: (X Y : Center C) (U : C)
  proof: rfl

中文:
定理 tensor_β
  条件: (X Y : 中心 C) (U : C)
  证明: rfl
-/
theorem tensor_β (X Y : Center C) (U : C) :
    (X otimes Y).2.β U =
      α_ _ _ _ ≪≫
        (whiskerLeftIso X.1 (Y.2.β U)) ≪≫ (α_ _ _ _).symm ≪≫
          (whiskerRightIso (X.2.β U) Y.1) ≪≫ α_ _ _ _ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `whiskerLeft_f` / 定理 `whiskerLeft_f`

English:
theorem whiskerLeft_f
  given: (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂)
  statement: (X ◁ f).f = X.1 ◁ f.f
  proof: rfl

中文:
定理 whiskerLeft_f
  条件: (X : 中心 C) {Y₁ Y₂ : 中心 C} (f : Y₁ ⟶ Y₂)
  结论: (X ◁ f).f = X.1 ◁ f.f
  证明: rfl
-/
theorem whiskerLeft_f (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) : (X ◁ f).f = X.1 ◁ f.f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `whiskerRight_f` / 定理 `whiskerRight_f`

English:
theorem whiskerRight_f
  given: {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C)
  statement: (f ▷ Y).f = f.f ▷ Y.1
  proof: rfl

中文:
定理 whiskerRight_f
  条件: {X₁ X₂ : 中心 C} (f : X₁ ⟶ X₂) (Y : 中心 C)
  结论: (f ▷ Y).f = f.f ▷ Y.1
  证明: rfl
-/
theorem whiskerRight_f {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) : (f ▷ Y).f = f.f ▷ Y.1 :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `tensor_f` / 定理 `tensor_f`

English:
theorem tensor_f
  given: {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  statement: (f otimesₘ g).f = f.f otimesₘ g.f
  proof: rfl

中文:
定理 tensor_f
  条件: {X₁ Y₁ X₂ Y₂ : 中心 C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  结论: (f otimesₘ g).f = f.f otimesₘ g.f
  证明: rfl
-/
theorem tensor_f {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f otimesₘ g).f = f.f otimesₘ g.f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `tensorUnit_β` / 定理 `tensorUnit_β`

English:
theorem tensorUnit_β
  given: (U : C)
  statement: (𝟙_ (Center C)).2.β U = fun_ U ≪≫ (ρ_ U).symm
  proof: rfl

中文:
定理 tensorUnit_β
  条件: (U : C)
  结论: (𝟙_ (中心 C)).2.β U = fun_ U ≪≫ (ρ_ U).symm
  证明: rfl
-/
theorem tensorUnit_β (U : C) : (𝟙_ (Center C)).2.β U = fun_ U ≪≫ (ρ_ U).symm :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `associator_hom_f` / 定理 `associator_hom_f`

English:
theorem associator_hom_f
  given: (X Y Z : Center C)
  statement: Hom.f (α_ X Y Z).hom = (α_ X.1 Y.1 Z.1).hom
  proof: rfl

中文:
定理 associator_hom_f
  条件: (X Y Z : 中心 C)
  结论: 态射.f (α_ X Y Z).hom = (α_ X.1 Y.1 Z.1).hom
  证明: rfl
-/
theorem associator_hom_f (X Y Z : Center C) : Hom.f (α_ X Y Z).hom = (α_ X.1 Y.1 Z.1).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `associator_inv_f` / 定理 `associator_inv_f`

English:
theorem associator_inv_f
  given: (X Y Z : Center C)
  statement: Hom.f (α_ X Y Z).inv = (α_ X.1 Y.1 Z.1).inv
  proof: by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← associator_hom_f]; rw [← comp_f]; rw [Iso.hom_inv_id]; rfl

中文:
定理 associator_inv_f
  条件: (X Y Z : 中心 C)
  结论: 态射.f (α_ X Y Z).inv = (α_ X.1 Y.1 Z.1).inv
  证明: by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← associator_hom_f]; rw [← comp_f]; rw [Iso.hom_inv_id]; rfl

Depends on / 依赖: Iso.hom_inv_id, Iso.inv_ext, Originally, Porting, associator_hom_f, community, comp_f, github, github.com, hom_inv_id, inv_ext, issues, leanprover, mathlib4
-/
theorem associator_inv_f (X Y Z : Center C) : Hom.f (α_ X Y Z).inv = (α_ X.1 Y.1 Z.1).inv := by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← associator_hom_f]; rw [← comp_f]; rw [Iso.hom_inv_id]; rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `leftUnitor_hom_f` / 定理 `leftUnitor_hom_f`

English:
theorem leftUnitor_hom_f
  given: (X : Center C)
  statement: Hom.f (fun_ X).hom = (fun_ X.1).hom
  proof: rfl

中文:
定理 leftUnitor_hom_f
  条件: (X : 中心 C)
  结论: 态射.f (fun_ X).hom = (fun_ X.1).hom
  证明: rfl
-/
theorem leftUnitor_hom_f (X : Center C) : Hom.f (fun_ X).hom = (fun_ X.1).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `leftUnitor_inv_f` / 定理 `leftUnitor_inv_f`

English:
theorem leftUnitor_inv_f
  given: (X : Center C)
  statement: Hom.f (fun_ X).inv = (fun_ X.1).inv
  proof: by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← leftUnitor_hom_f]; rw [← comp_f]; rw [Iso.hom_inv_id]; rfl

中文:
定理 leftUnitor_inv_f
  条件: (X : 中心 C)
  结论: 态射.f (fun_ X).inv = (fun_ X.1).inv
  证明: by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← leftUnitor_hom_f]; rw [← comp_f]; rw [Iso.hom_inv_id]; rfl

Depends on / 依赖: Iso.hom_inv_id, Iso.inv_ext, Originally, Porting, community, comp_f, github, github.com, hom_inv_id, inv_ext, issues, leanprover, leftUnitor_hom_f, mathlib4
-/
theorem leftUnitor_inv_f (X : Center C) : Hom.f (fun_ X).inv = (fun_ X.1).inv := by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← leftUnitor_hom_f]; rw [← comp_f]; rw [Iso.hom_inv_id]; rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `rightUnitor_hom_f` / 定理 `rightUnitor_hom_f`

English:
theorem rightUnitor_hom_f
  given: (X : Center C)
  statement: Hom.f (ρ_ X).hom = (ρ_ X.1).hom
  proof: rfl

中文:
定理 rightUnitor_hom_f
  条件: (X : 中心 C)
  结论: 态射.f (ρ_ X).hom = (ρ_ X.1).hom
  证明: rfl
-/
theorem rightUnitor_hom_f (X : Center C) : Hom.f (ρ_ X).hom = (ρ_ X.1).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `rightUnitor_inv_f` / 定理 `rightUnitor_inv_f`

English:
theorem rightUnitor_inv_f
  given: (X : Center C)
  statement: Hom.f (ρ_ X).inv = (ρ_ X.1).inv
  proof: by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← rightUnitor_hom_f]; rw [← comp_f]; rw [Iso.hom_inv_id]; rfl

中文:
定理 rightUnitor_inv_f
  条件: (X : 中心 C)
  结论: 态射.f (ρ_ X).inv = (ρ_ X.1).inv
  证明: by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← rightUnitor_hom_f]; rw [← comp_f]; rw [Iso.hom_inv_id]; rfl

Depends on / 依赖: Iso.hom_inv_id, Iso.inv_ext, Originally, Porting, community, comp_f, github, github.com, hom_inv_id, inv_ext, issues, leanprover, mathlib4, rightUnitor_hom_f
-/
theorem rightUnitor_inv_f (X : Center C) : Hom.f (ρ_ X).inv = (ρ_ X.1).inv := by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← rightUnitor_hom_f]; rw [← comp_f]; rw [Iso.hom_inv_id]; rfl

end

section

variable (C)

/-- The forgetful monoidal functor from the Drinfeld center to the original category. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Center C ⥤ C where
  body: X.1
  map f := f.f

中文:
定义 forget
  签名: : 中心 C ⥤ C where
  定义体: X.1
  map f := f.f
-/
def forget : Center C ⥤ C where
  obj X := X.1
  map f := f.f

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget C).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

中文:
实例 :
  签名: (forget C).幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, Iso.refl, toMonoidal
-/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `forget_ε` / 引理 `forget_ε`

English:
lemma forget_ε
  statement: ε (forget C) = 𝟙 _
  proof: rfl

中文:
引理 forget_ε
  结论: ε (forget C) = 𝟙 _
  证明: rfl
-/
@[simp] lemma forget_ε : ε (forget C) = 𝟙 _ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `forget_η` / 引理 `forget_η`

English:
lemma forget_η
  statement: η (forget C) = 𝟙 _
  proof: rfl

中文:
引理 forget_η
  结论: η (forget C) = 𝟙 _
  证明: rfl
-/
@[simp] lemma forget_η : η (forget C) = 𝟙 _ := rfl

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `forget_μ` / 引理 `forget_μ`

English:
lemma forget_μ
  given: (X Y : Center C)
  statement: μ (forget C) X Y = 𝟙 _
  proof: rfl

中文:
引理 forget_μ
  条件: (X Y : 中心 C)
  结论: μ (forget C) X Y = 𝟙 _
  证明: rfl
-/
@[simp] lemma forget_μ (X Y : Center C) : μ (forget C) X Y = 𝟙 _ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `forget_δ` / 引理 `forget_δ`

English:
lemma forget_δ
  given: (X Y : Center C)
  statement: δ (forget C) X Y = 𝟙 _
  proof: rfl

中文:
引理 forget_δ
  条件: (X Y : 中心 C)
  结论: δ (forget C) X Y = 𝟙 _
  证明: rfl
-/
@[simp] lemma forget_δ (X Y : Center C) : δ (forget C) X Y = 𝟙 _ := rfl

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget C).ReflectsIsomorphisms
  body: by dsimp at i; change IsIso (isoMk f).hom; infer_instance

中文:
实例 :
  签名: (forget C).反映同构
  定义体: by dsimp at i; change IsIso (isoMk f).hom; infer_instance

Depends on / 依赖: infer_instance
-/
instance : (forget C).ReflectsIsomorphisms where
  reflects f i := by dsimp at i; change IsIso (isoMk f).hom; infer_instance

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for the `BraidedCategory` instance on `Center C`. -/
@[simps!]
/--
Definition of `braiding` / `braiding` 的定义

English:
definition braiding
  signature: (X Y : Center C)
  body: isoMk
    ⟨(X.2.β Y.1).hom, fun U => by
      dsimp
      simp only [Category.assoc]
      rw [← IsIso.inv_comp_eq]; rw [IsIso.Iso.inv_hom]; rw [← HalfBraiding.monoidal_assoc]; rw [← HalfBraiding.naturality_assoc]; rw [HalfBraiding.monoidal]
      simp⟩

中文:
定义 braiding
  签名: (X Y : 中心 C)
  定义体: isoMk
    ⟨(X.2.β Y.1).hom, fun U => by
      dsimp
      simp only [Category.assoc]
      rw [← IsIso.inv_comp_eq]; rw [IsIso.Iso.inv_hom]; rw [← HalfBraiding.monoidal_assoc]; rw [← HalfBraiding.naturality_assoc]; rw [HalfBraiding.monoidal]
      simp⟩

Depends on / 依赖: Category, Category.assoc, HalfBraiding, HalfBraiding.monoidal, HalfBraiding.monoidal_assoc, HalfBraiding.naturality_assoc, IsIso.Iso.inv_hom, IsIso.inv_comp_eq, inv_comp_eq, inv_hom, monoidal, monoidal_assoc, naturality_assoc
-/
def braiding (X Y : Center C) : X otimes Y ≅ Y otimes X :=
  isoMk
    ⟨(X.2.β Y.1).hom, fun U => by
      dsimp
      simp only [Category.assoc]
      rw [← IsIso.inv_comp_eq]; rw [IsIso.Iso.inv_hom]; rw [← HalfBraiding.monoidal_assoc]; rw [← HalfBraiding.naturality_assoc]; rw [HalfBraiding.monoidal]
      simp⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `braidedCategoryCenter` / 实例 `braidedCategoryCenter`

English:
instance braidedCategoryCenter
  signature: : BraidedCategory (Center C) where
  body: braiding

中文:
实例 braidedCategoryCenter
  签名: : 辫范畴 (中心 C) where
  定义体: braiding

Depends on / 依赖: braiding
-/
instance braidedCategoryCenter : BraidedCategory (Center C) where
  braiding := braiding

-- `cat_disch` handles the hexagon axioms
section

variable [BraidedCategory C]

open BraidedCategory

/-- Auxiliary construction for `ofBraided`. -/
@[simps]
/--
Definition of `ofBraidedObj` / `ofBraidedObj` 的定义

English:
definition ofBraidedObj
  signature: (X : C)
  body: ⟨X, { β := fun Y => β_ X Y}⟩

中文:
定义 ofBraidedObj
  签名: (X : C)
  定义体: ⟨X, { β := fun Y => β_ X Y}⟩
-/
def ofBraidedObj (X : C) : Center C :=
  ⟨X, { β := fun Y => β_ X Y}⟩

variable (C)

/-- The functor lifting a braided category to its center, using the braiding as the half-braiding.
-/
@[simps]
/--
Definition of `ofBraided` / `ofBraided` 的定义

English:
definition ofBraided
  signature: : C ⥤ Center C where
  body: ofBraidedObj
  map f :=
    { f
      comm := fun U => braiding_naturality_left f U }

中文:
定义 ofBraided
  签名: : C ⥤ 中心 C where
  定义体: ofBraidedObj
  map f :=
    { f
      comm := fun U => braiding_naturality_left f U }

Depends on / 依赖: ofBraidedObj
-/
def ofBraided : C ⥤ Center C where
  obj := ofBraidedObj
  map f :=
    { f
      comm := fun U => braiding_naturality_left f U }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ofBraided C).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso :=
        { hom := { f := 𝟙 _ }
          inv := { f := 𝟙 _ } }
      μIso := fun _ _ =>
        { hom := { f := 𝟙 _ }
          inv := { f := 𝟙 _ } } }

中文:
实例 :
  签名: (ofBraided C).幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso :=
        { hom := { f := 𝟙 _ }
          inv := { f := 𝟙 _ } }
      μIso := fun _ _ =>
        { hom := { f := 𝟙 _ }
          inv := { f := 𝟙 _ } } }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, toMonoidal
-/
instance : (ofBraided C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso :=
        { hom := { f := 𝟙 _ }
          inv := { f := 𝟙 _ } }
      μIso := fun _ _ =>
        { hom := { f := 𝟙 _ }
          inv := { f := 𝟙 _ } } }

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ofBraided_ε_f` / 引理 `ofBraided_ε_f`

English:
lemma ofBraided_ε_f
  statement: (ε (ofBraided C)).f = 𝟙 _
  proof: rfl

中文:
引理 ofBraided_ε_f
  结论: (ε (ofBraided C)).f = 𝟙 _
  证明: rfl
-/
@[simp] lemma ofBraided_ε_f : (ε (ofBraided C)).f = 𝟙 _ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ofBraided_η_f` / 引理 `ofBraided_η_f`

English:
lemma ofBraided_η_f
  statement: (η (ofBraided C)).f = 𝟙 _
  proof: rfl

中文:
引理 ofBraided_η_f
  结论: (η (ofBraided C)).f = 𝟙 _
  证明: rfl
-/
@[simp] lemma ofBraided_η_f : (η (ofBraided C)).f = 𝟙 _ := rfl

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ofBraided_μ_f` / 引理 `ofBraided_μ_f`

English:
lemma ofBraided_μ_f
  given: (X Y : C)
  statement: (μ (ofBraided C) X Y).f = 𝟙 _
  proof: rfl

中文:
引理 ofBraided_μ_f
  条件: (X Y : C)
  结论: (μ (ofBraided C) X Y).f = 𝟙 _
  证明: rfl
-/
@[simp] lemma ofBraided_μ_f (X Y : C) : (μ (ofBraided C) X Y).f = 𝟙 _ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ofBraided_δ_f` / 引理 `ofBraided_δ_f`

English:
lemma ofBraided_δ_f
  given: (X Y : C)
  statement: (δ (ofBraided C) X Y).f = 𝟙 _
  proof: rfl

中文:
引理 ofBraided_δ_f
  条件: (X Y : C)
  结论: (δ (ofBraided C) X Y).f = 𝟙 _
  证明: rfl
-/
@[simp] lemma ofBraided_δ_f (X Y : C) : (δ (ofBraided C) X Y).f = 𝟙 _ := rfl

end

end Center

end CategoryTheory
