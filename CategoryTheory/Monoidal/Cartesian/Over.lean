/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!

# `CartesianMonoidalCategory` for `Over X`

We provide a `CartesianMonoidalCategory (Over X)` instance via pullbacks, and provide simp lemmas
for the induced `MonoidalCategory (Over X)` instance.

-/

public noncomputable section

namespace CategoryTheory.Over

open CategoryTheory.Functor Limits CartesianMonoidalCategory

variable {C : Type*} [Category* C] [HasPullbacks C]

/--
Definition of `cartesianMonoidalCategory` / `cartesianMonoidalCategory` 的定义

English:
abbreviation cartesianMonoidalCategory
  signature: (X : C)
  body: .ofChosenFiniteProducts
    ⟨asEmptyCone (Over.mk (𝟙 X)), IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom)
      fun Y m => Over.OverMorphism.ext (by simpa using m.w)⟩
    fun Y Z => ⟨pullbackConeEquivBinaryFan.functor.obj (pullback.cone Y.hom Z.hom),
    (pullback.isLimit _ _).pullbackConeEquivBi

中文:
缩写 cartesianMonoidalCategory
  签名: (X : C)
  定义体: .ofChosenFiniteProducts
    ⟨asEmptyCone (Over.mk (𝟙 X)), IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom)
      fun Y m => Over.OverMorphism.ext (by simpa using m.w)⟩
    fun Y Z => ⟨pullbackConeEquivBinaryFan.functor.obj (pullback.cone Y.hom Z.hom),
    (pullback.isLimit _ _).pullbackConeEquivBi

Depends on / 依赖: IsTerminal, IsTerminal.ofUniqueHom, Over.OverMorphism.ext, Over.homMk, Over.mk, OverMorphism, Y.hom, Z.hom, asEmptyCone, functor, isLimit, ofChosenFiniteProducts, ofUniqueHom, pullback, pullback.cone, pullback.isLimit, pullbackConeEquivBinaryFan, pullbackConeEquivBinaryFan.functor.obj, pullbackConeEquivBinaryFanFunctor
-/
abbrev cartesianMonoidalCategory (X : C) : CartesianMonoidalCategory (Over X) :=
  .ofChosenFiniteProducts
    ⟨asEmptyCone (Over.mk (𝟙 X)), IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom)
      fun Y m => Over.OverMorphism.ext (by simpa using m.w)⟩
    fun Y Z => ⟨pullbackConeEquivBinaryFan.functor.obj (pullback.cone Y.hom Z.hom),
    (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor⟩

attribute [local instance] cartesianMonoidalCategory

/--
Definition of `braidedCategory` / `braidedCategory` 的定义

English:
abbreviation braidedCategory
  signature: (X : C)
  body: .ofCartesianMonoidalCategory

中文:
缩写 braidedCategory
  签名: (X : C)
  定义体: .ofCartesianMonoidalCategory

Depends on / 依赖: ofCartesianMonoidalCategory
-/
abbrev braidedCategory (X : C) : BraidedCategory (Over X) :=
  .ofCartesianMonoidalCategory

attribute [local instance] braidedCategory

open MonoidalCategory

variable {X : C}

@[ext]
/--
lemma `tensorObj_ext` / 引理 `tensorObj_ext`

English:
lemma tensorObj_ext
  statement: {R : C} {S T : Over X} (f₁ f₂ : R ⟶ (S otimes T).left)
  proof: pullback.hom_ext e₁ e₂

@[simp]

中文:
引理 tensorObj_ext
  结论: {R : C} {S T : Over X} (f₁ f₂ : R ⟶ (S otimes T).left)
  证明: pullback.hom_ext e₁ e₂

@[simp]

Depends on / 依赖: hom_ext, pullback, pullback.hom_ext
-/
lemma tensorObj_ext {R : C} {S T : Over X} (f₁ f₂ : R ⟶ (S otimes T).left)
    (e₁ : f₁ ≫ pullback.fst _ _ = f₂ ≫ pullback.fst _ _)
    (e₂ : f₁ ≫ pullback.snd _ _ = f₂ ≫ pullback.snd _ _) : f₁ = f₂ :=
  pullback.hom_ext e₁ e₂

@[simp]
/--
lemma `tensorObj_left` / 引理 `tensorObj_left`

English:
lemma tensorObj_left
  given: (R S : Over X)
  statement: (R otimes S).left = Limits.pullback R.hom S.hom
  proof: rfl

@[simp]

中文:
引理 tensorObj_left
  条件: (R S : Over X)
  结论: (R otimes S).left = Limits.pullback R.hom S.hom
  证明: rfl

@[simp]
-/
lemma tensorObj_left (R S : Over X) : (R otimes S).left = Limits.pullback R.hom S.hom := rfl

@[simp]
/--
lemma `tensorObj_hom` / 引理 `tensorObj_hom`

English:
lemma tensorObj_hom
  given: (R S : Over X)
  statement: (R otimes S).hom = pullback.fst R.hom S.hom ≫ R.hom
  proof: rfl

@[simp]

中文:
引理 tensorObj_hom
  条件: (R S : Over X)
  结论: (R otimes S).hom = pullback.fst R.hom S.hom ≫ R.hom
  证明: rfl

@[simp]
-/
lemma tensorObj_hom (R S : Over X) : (R otimes S).hom = pullback.fst R.hom S.hom ≫ R.hom := rfl

@[simp]
/--
lemma `tensorUnit_left` / 引理 `tensorUnit_left`

English:
lemma tensorUnit_left
  statement: (𝟙_ (Over X)).left = X
  proof: rfl

@[simp]

中文:
引理 tensorUnit_left
  结论: (𝟙_ (Over X)).left = X
  证明: rfl

@[simp]
-/
lemma tensorUnit_left : (𝟙_ (Over X)).left = X := rfl

@[simp]
/--
lemma `tensorUnit_hom` / 引理 `tensorUnit_hom`

English:
lemma tensorUnit_hom
  statement: (𝟙_ (Over X)).hom = 𝟙 X
  proof: rfl

@[simp]

中文:
引理 tensorUnit_hom
  结论: (𝟙_ (Over X)).hom = 𝟙 X
  证明: rfl

@[simp]
-/
lemma tensorUnit_hom : (𝟙_ (Over X)).hom = 𝟙 X := rfl

@[simp]
/--
lemma `lift_left` / 引理 `lift_left`

English:
lemma lift_left
  given: {R S T : Over X} (f : R ⟶ S) (g : R ⟶ T)
  proof: rfl

@[simp]

中文:
引理 lift_left
  条件: {R S T : Over X} (f : R ⟶ S) (g : R ⟶ T)
  证明: rfl

@[simp]
-/
lemma lift_left {R S T : Over X} (f : R ⟶ S) (g : R ⟶ T) :
    (lift f g).left = pullback.lift f.left g.left (f.w.trans g.w.symm) := rfl

@[simp]
/--
lemma `fst_left` / 引理 `fst_left`

English:
lemma fst_left
  given: {R S : Over X}
  statement: (fst R S).left = pullback.fst _ _
  proof: rfl

@[simp]

中文:
引理 fst_left
  条件: {R S : Over X}
  结论: (fst R S).left = pullback.fst _ _
  证明: rfl

@[simp]
-/
lemma fst_left {R S : Over X} : (fst R S).left = pullback.fst _ _ := rfl

@[simp]
/--
lemma `snd_left` / 引理 `snd_left`

English:
lemma snd_left
  given: {R S : Over X}
  statement: (snd R S).left = pullback.snd _ _
  proof: rfl

@[simp]

中文:
引理 snd_left
  条件: {R S : Over X}
  结论: (snd R S).left = pullback.snd _ _
  证明: rfl

@[simp]
-/
lemma snd_left {R S : Over X} : (snd R S).left = pullback.snd _ _ := rfl

@[simp]
/--
lemma `toUnit_left` / 引理 `toUnit_left`

English:
lemma toUnit_left
  given: {R : Over X}
  statement: (toUnit R).left = R.hom
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 toUnit_left
  条件: {R : Over X}
  结论: (toUnit R).left = R.hom
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma toUnit_left {R : Over X} : (toUnit R).left = R.hom := rfl

@[reassoc (attr := simp)]
/--
lemma `associator_hom_left_fst` / 引理 `associator_hom_left_fst`

English:
lemma associator_hom_left_fst
  given: (R S T : Over X)
  proof: limit.lift_π _ _

@[reassoc (attr := simp)]

中文:
引理 associator_hom_left_fst
  条件: (R S T : Over X)
  证明: limit.lift_π _ _

@[reassoc (attr := simp)]

Depends on / 依赖: limit.lift_
-/
lemma associator_hom_left_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.fst _ (pullback.fst _ _ ≫ _) =
      pullback.fst _ _ ≫ pullback.fst _ _ :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
/--
lemma `associator_hom_left_snd_fst` / 引理 `associator_hom_left_snd_fst`

English:
lemma associator_hom_left_snd_fst
  given: (R S T : Over X)
  proof: (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]

中文:
引理 associator_hom_left_snd_fst
  条件: (R S T : Over X)
  证明: (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]

Depends on / 依赖: limit.lift_
-/
lemma associator_hom_left_snd_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.snd _ (pullback.fst _ _ ≫ _) ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
/--
lemma `associator_hom_left_snd_snd` / 引理 `associator_hom_left_snd_snd`

English:
lemma associator_hom_left_snd_snd
  given: (R S T : Over X)
  proof: (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]

中文:
引理 associator_hom_left_snd_snd
  条件: (R S T : Over X)
  证明: (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]

Depends on / 依赖: limit.lift_
-/
lemma associator_hom_left_snd_snd (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.snd _ (pullback.fst _ _ ≫ _) ≫ pullback.snd _ _ =
      pullback.snd _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
/--
lemma `associator_inv_left_fst_fst` / 引理 `associator_inv_left_fst_fst`

English:
lemma associator_inv_left_fst_fst
  given: (R S T : Over X)
  proof: (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]

中文:
引理 associator_inv_left_fst_fst
  条件: (R S T : Over X)
  证明: (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]

Depends on / 依赖: limit.lift_
-/
lemma associator_inv_left_fst_fst (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.fst (pullback.fst _ _ ≫ _) _ ≫ pullback.fst _ _ =
      pullback.fst _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
/--
lemma `associator_inv_left_fst_snd` / 引理 `associator_inv_left_fst_snd`

English:
lemma associator_inv_left_fst_snd
  given: (R S T : Over X)
  proof: (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]

中文:
引理 associator_inv_left_fst_snd
  条件: (R S T : Over X)
  证明: (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]

Depends on / 依赖: limit.lift_
-/
lemma associator_inv_left_fst_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.fst (pullback.fst _ _ ≫ _) _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
/--
lemma `associator_inv_left_snd` / 引理 `associator_inv_left_snd`

English:
lemma associator_inv_left_snd
  given: (R S T : Over X)
  proof: limit.lift_π _ _

@[simp]

中文:
引理 associator_inv_left_snd
  条件: (R S T : Over X)
  证明: limit.lift_π _ _

@[simp]

Depends on / 依赖: limit.lift_
-/
lemma associator_inv_left_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.snd (pullback.fst _ _ ≫ _) _ =
      pullback.snd _ _ ≫ pullback.snd _ _ :=
  limit.lift_π _ _

@[simp]
/--
lemma `leftUnitor_hom_left` / 引理 `leftUnitor_hom_left`

English:
lemma leftUnitor_hom_left
  given: (Y : Over X)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 leftUnitor_hom_left
  条件: (Y : Over X)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma leftUnitor_hom_left (Y : Over X) :
    (fun_ Y).hom.left = pullback.snd _ _ := rfl

@[reassoc (attr := simp)]
/--
lemma `leftUnitor_inv_left_fst` / 引理 `leftUnitor_inv_left_fst`

English:
lemma leftUnitor_inv_left_fst
  given: (Y : Over X)
  proof: limit.lift_π _ _

@[reassoc (attr := simp)]

中文:
引理 leftUnitor_inv_left_fst
  条件: (Y : Over X)
  证明: limit.lift_π _ _

@[reassoc (attr := simp)]

Depends on / 依赖: limit.lift_
-/
lemma leftUnitor_inv_left_fst (Y : Over X) :
    (fun_ Y).inv.left ≫ pullback.fst (𝟙 X) _ = Y.hom :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
/--
lemma `leftUnitor_inv_left_snd` / 引理 `leftUnitor_inv_left_snd`

English:
lemma leftUnitor_inv_left_snd
  given: (Y : Over X)
  proof: limit.lift_π _ _

@[simp]

中文:
引理 leftUnitor_inv_left_snd
  条件: (Y : Over X)
  证明: limit.lift_π _ _

@[simp]

Depends on / 依赖: limit.lift_
-/
lemma leftUnitor_inv_left_snd (Y : Over X) :
    (fun_ Y).inv.left ≫ pullback.snd (𝟙 X) _ = 𝟙 Y.left :=
  limit.lift_π _ _

@[simp]
/--
lemma `rightUnitor_hom_left` / 引理 `rightUnitor_hom_left`

English:
lemma rightUnitor_hom_left
  given: (Y : Over X)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 rightUnitor_hom_left
  条件: (Y : Over X)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma rightUnitor_hom_left (Y : Over X) :
    (ρ_ Y).hom.left = pullback.fst _ (𝟙 X) := rfl

@[reassoc (attr := simp)]
/--
lemma `rightUnitor_inv_left_fst` / 引理 `rightUnitor_inv_left_fst`

English:
lemma rightUnitor_inv_left_fst
  given: (Y : Over X)
  proof: limit.lift_π _ _

@[reassoc (attr := simp)]

中文:
引理 rightUnitor_inv_left_fst
  条件: (Y : Over X)
  证明: limit.lift_π _ _

@[reassoc (attr := simp)]

Depends on / 依赖: limit.lift_, sheafToPresheaf
-/
lemma rightUnitor_inv_left_fst (Y : Over X) :
    (ρ_ Y).inv.left ≫ pullback.fst _ (𝟙 X) = 𝟙 _ :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
/--
lemma `rightUnitor_inv_left_snd` / 引理 `rightUnitor_inv_left_snd`

English:
lemma rightUnitor_inv_left_snd
  given: (Y : Over X)
  proof: limit.lift_π _ _

中文:
引理 rightUnitor_inv_left_snd
  条件: (Y : Over X)
  证明: limit.lift_π _ _

Depends on / 依赖: limit.lift_
-/
lemma rightUnitor_inv_left_snd (Y : Over X) :
    (ρ_ Y).inv.left ≫ pullback.snd _ (𝟙 X) = Y.hom :=
  limit.lift_π _ _

/--
lemma `whiskerLeft_left` / 引理 `whiskerLeft_left`

English:
lemma whiskerLeft_left
  given: {R S T : Over X} (f : S ⟶ T)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_left
  条件: {R S T : Over X} (f : S ⟶ T)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma whiskerLeft_left {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left = pullback.map _ _ _ _ (𝟙 _) f.left (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_left_fst` / 引理 `whiskerLeft_left_fst`

English:
lemma whiskerLeft_left_fst
  given: {R S T : Over X} (f : S ⟶ T)
  proof: (limit.lift_π _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_left_fst
  条件: {R S T : Over X} (f : S ⟶ T)
  证明: (limit.lift_π _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.comp_id, comp_id, limit.lift_
-/
lemma whiskerLeft_left_fst {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (limit.lift_π _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_left_snd` / 引理 `whiskerLeft_left_snd`

English:
lemma whiskerLeft_left_snd
  given: {R S T : Over X} (f : S ⟶ T)
  proof: limit.lift_π _ _

中文:
引理 whiskerLeft_left_snd
  条件: {R S T : Over X} (f : S ⟶ T)
  证明: limit.lift_π _ _

Depends on / 依赖: limit.lift_
-/
lemma whiskerLeft_left_snd {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ pullback.snd _ _ = pullback.snd _ _ ≫ f.left :=
  limit.lift_π _ _

/--
lemma `whiskerRight_left` / 引理 `whiskerRight_left`

English:
lemma whiskerRight_left
  given: {R S T : Over X} (f : S ⟶ T)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 whiskerRight_left
  条件: {R S T : Over X} (f : S ⟶ T)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma whiskerRight_left {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left = pullback.map _ _ _ _ f.left (𝟙 _) (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
/--
lemma `whiskerRight_left_fst` / 引理 `whiskerRight_left_fst`

English:
lemma whiskerRight_left_fst
  given: {R S T : Over X} (f : S ⟶ T)
  proof: limit.lift_π _ _

@[reassoc (attr := simp)]

中文:
引理 whiskerRight_left_fst
  条件: {R S T : Over X} (f : S ⟶ T)
  证明: limit.lift_π _ _

@[reassoc (attr := simp)]

Depends on / 依赖: limit.lift_
-/
lemma whiskerRight_left_fst {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.left :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
/--
lemma `whiskerRight_left_snd` / 引理 `whiskerRight_left_snd`

English:
lemma whiskerRight_left_snd
  given: {R S T : Over X} (f : S ⟶ T)
  proof: (limit.lift_π _ _).trans (Category.comp_id _)

中文:
引理 whiskerRight_left_snd
  条件: {R S T : Over X} (f : S ⟶ T)
  证明: (limit.lift_π _ _).trans (Category.comp_id _)

Depends on / 依赖: Category, Category.comp_id, comp_id, limit.lift_
-/
lemma whiskerRight_left_snd {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (limit.lift_π _ _).trans (Category.comp_id _)

/--
lemma `tensorHom_left` / 引理 `tensorHom_left`

English:
lemma tensorHom_left
  given: {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 tensorHom_left
  条件: {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma tensorHom_left {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f otimesₘ g).left = pullback.map _ _ _ _ f.left g.left (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
/--
lemma `tensorHom_left_fst` / 引理 `tensorHom_left_fst`

English:
lemma tensorHom_left_fst
  statement: {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X)
  proof: limit.lift_π _ _

@[reassoc (attr := simp)]

中文:
引理 tensorHom_left_fst
  结论: {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X)
  证明: limit.lift_π _ _

@[reassoc (attr := simp)]

Depends on / 依赖: limit.lift_
-/
lemma tensorHom_left_fst {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X)
    (f : R ⟶ mk fS) (g : T ⟶ mk fU) :
    (f otimesₘ g).left ≫ pullback.fst fS fU = pullback.fst R.hom T.hom ≫ f.left :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
/--
lemma `tensorHom_left_snd` / 引理 `tensorHom_left_snd`

English:
lemma tensorHom_left_snd
  statement: {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X)
  proof: limit.lift_π _ _

@[simp]

中文:
引理 tensorHom_left_snd
  结论: {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X)
  证明: limit.lift_π _ _

@[simp]

Depends on / 依赖: limit.lift_
-/
lemma tensorHom_left_snd {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X)
    (f : R ⟶ mk fS) (g : T ⟶ mk fU) :
    (f otimesₘ g).left ≫ pullback.snd fS fU = pullback.snd R.hom T.hom ≫ g.left :=
  limit.lift_π _ _

@[simp]
/--
lemma `braiding_hom_left` / 引理 `braiding_hom_left`

English:
lemma braiding_hom_left
  given: {R S : Over X}
  proof: rfl

@[simp]

中文:
引理 braiding_hom_left
  条件: {R S : Over X}
  证明: rfl

@[simp]
-/
lemma braiding_hom_left {R S : Over X} :
    (β_ R S).hom.left = (pullbackSymmetry _ _).hom := rfl

@[simp]
/--
lemma `braiding_inv_left` / 引理 `braiding_inv_left`

English:
lemma braiding_inv_left
  given: {R S : Over X}
  proof: rfl

中文:
引理 braiding_inv_left
  条件: {R S : Over X}
  证明: rfl
-/
lemma braiding_inv_left {R S : Over X} :
    (β_ R S).inv.left = (pullbackSymmetry _ _).hom := rfl

variable {A B R S Y Z : C} {f : R ⟶ X} {g : S ⟶ X}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Over.pullback f).Braided
  body: .ofChosenFiniteProducts _

@[simp]

中文:
实例 :
  签名: (Over.pullback f).辫
  定义体: .ofChosenFiniteProducts _

@[simp]

Depends on / 依赖: ofChosenFiniteProducts
-/
instance : (Over.pullback f).Braided := .ofChosenFiniteProducts _

@[simp]
/--
lemma `η_pullback_left` / 引理 `η_pullback_left`

English:
lemma η_pullback_left
  statement: (OplaxMonoidal.η (Over.pullback f)).left = (pullback.snd (𝟙 _) f)
  proof: rfl

@[simp]

中文:
引理 η_pullback_left
  结论: (反松弛幺半群.η (Over.pullback f)).left = (pullback.snd (𝟙 _) f)
  证明: rfl

@[simp]
-/
lemma η_pullback_left : (OplaxMonoidal.η (Over.pullback f)).left = (pullback.snd (𝟙 _) f) := rfl

@[simp]
/--
lemma `ε_pullback_left` / 引理 `ε_pullback_left`

English:
lemma ε_pullback_left
  statement: (LaxMonoidal.ε (Over.pullback f)).left = inv (pullback.snd (𝟙 _) f)
  proof: by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← η_pullback_left]; rw [← Over.comp_left]; rw [Monoidal.η_ε]; rw [Over.id_left]

中文:
引理 ε_pullback_left
  结论: (松弛幺半群.ε (Over.pullback f)).left = inv (pullback.snd (𝟙 _) f)
  证明: by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← η_pullback_left]; rw [← Over.comp_left]; rw [Monoidal.η_ε]; rw [Over.id_left]

Depends on / 依赖: IsIso.eq_inv_of_hom_inv_id, Monoidal, Over.comp_left, Over.id_left, comp_left, eq_inv_of_hom_inv_id, id_left
-/
lemma ε_pullback_left : (LaxMonoidal.ε (Over.pullback f)).left = inv (pullback.snd (𝟙 _) f) := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← η_pullback_left]; rw [← Over.comp_left]; rw [Monoidal.η_ε]; rw [Over.id_left]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `μ_pullback_left_fst_fst` / 引理 `μ_pullback_left_fst_fst`

English:
lemma μ_pullback_left_fst_fst
  given: (R S : Over X)
  proof: by
  rw [Monoidal.μ_of_cartesianMonoidalCategory]; rw [← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left]; rw [← Over.comp_left_assoc]; rw [Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison, fst]

中文:
引理 μ_pullback_left_fst_fst
  条件: (R S : Over X)
  证明: by
  rw [Monoidal.μ_of_cartesianMonoidalCategory]; rw [← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left]; rw [← Over.comp_left_assoc]; rw [Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison, fst]

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.prodComparison, Iso.hom_inv_id, Monoidal, Over.comp_left_assoc, Over.pullback, cancel_epi, comp_left_assoc, hom.left, hom_inv_id, prodComparison, prodComparisonIso, pullback
-/
lemma μ_pullback_left_fst_fst (R S : Over X) :
    (LaxMonoidal.μ (Over.pullback f) R S).left ≫
      pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  rw [Monoidal.μ_of_cartesianMonoidalCategory]; rw [← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left]; rw [← Over.comp_left_assoc]; rw [Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison, fst]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `μ_pullback_left_fst_snd` / 引理 `μ_pullback_left_fst_snd`

English:
lemma μ_pullback_left_fst_snd
  given: (R S : Over X)
  proof: by
  rw [Monoidal.μ_of_cartesianMonoidalCategory]; rw [← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left]; rw [← Over.comp_left_assoc]; rw [Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison, snd]

中文:
引理 μ_pullback_left_fst_snd
  条件: (R S : Over X)
  证明: by
  rw [Monoidal.μ_of_cartesianMonoidalCategory]; rw [← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left]; rw [← Over.comp_left_assoc]; rw [Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison, snd]

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.prodComparison, Iso.hom_inv_id, Monoidal, Over.comp_left_assoc, Over.pullback, cancel_epi, comp_left_assoc, hom.left, hom_inv_id, prodComparison, prodComparisonIso, pullback
-/
lemma μ_pullback_left_fst_snd (R S : Over X) :
    (LaxMonoidal.μ (Over.pullback f) R S).left ≫
      pullback.fst _ _ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst _ _ := by
  rw [Monoidal.μ_of_cartesianMonoidalCategory]; rw [← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left]; rw [← Over.comp_left_assoc]; rw [Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison, snd]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `μ_pullback_left_snd` / 引理 `μ_pullback_left_snd`

English:
lemma μ_pullback_left_snd
  given: (R S : Over X)
  proof: by
  rw [Monoidal.μ_of_cartesianMonoidalCategory]; rw [← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left]; rw [← Over.comp_left_assoc]; rw [Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison]

@[simp]

中文:
引理 μ_pullback_left_snd
  条件: (R S : Over X)
  证明: by
  rw [Monoidal.μ_of_cartesianMonoidalCategory]; rw [← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left]; rw [← Over.comp_left_assoc]; rw [Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison]

@[simp]

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.prodComparison, Iso.hom_inv_id, Monoidal, Over.comp_left_assoc, Over.pullback, cancel_epi, comp_left_assoc, hom.left, hom_inv_id, prodComparison, prodComparisonIso, pullback
-/
lemma μ_pullback_left_snd (R S : Over X) :
    (LaxMonoidal.μ (Over.pullback f) R S).left ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [Monoidal.μ_of_cartesianMonoidalCategory]; rw [← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left]; rw [← Over.comp_left_assoc]; rw [Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison]

@[simp]
/--
lemma `μ_pullback_left_fst_fst'` / 引理 `μ_pullback_left_fst_fst'`

English:
lemma μ_pullback_left_fst_fst'
  given: (g₁ : Y ⟶ X) (g₂ : Z ⟶ X)
  proof: μ_pullback_left_fst_fst ..

@[simp]

中文:
引理 μ_pullback_left_fst_fst'
  条件: (g₁ : Y ⟶ X) (g₂ : Z ⟶ X)
  证明: μ_pullback_left_fst_fst ..

@[simp]

Depends on / 依赖: infer_instance
-/
lemma μ_pullback_left_fst_fst' (g₁ : Y ⟶ X) (g₂ : Z ⟶ X) :
    (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).left ≫
      pullback.fst (pullback.fst g₁ g₂ ≫ g₁) f ≫ pullback.fst g₁ g₂ =
        pullback.fst _ _ ≫ pullback.fst _ _ :=
  μ_pullback_left_fst_fst ..

@[simp]
/--
lemma `μ_pullback_left_fst_snd'` / 引理 `μ_pullback_left_fst_snd'`

English:
lemma μ_pullback_left_fst_snd'
  given: (g₁ : Y ⟶ X) (g₂ : Z ⟶ X)
  proof: μ_pullback_left_fst_snd ..

@[simp]

中文:
引理 μ_pullback_left_fst_snd'
  条件: (g₁ : Y ⟶ X) (g₂ : Z ⟶ X)
  证明: μ_pullback_left_fst_snd ..

@[simp]
-/
lemma μ_pullback_left_fst_snd' (g₁ : Y ⟶ X) (g₂ : Z ⟶ X) :
    (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).left ≫
      pullback.fst (pullback.fst g₁ g₂ ≫ g₁) f ≫ pullback.snd g₁ g₂ =
        pullback.snd _ _ ≫ pullback.fst _ _ :=
  μ_pullback_left_fst_snd ..

@[simp]
/--
lemma `μ_pullback_left_snd'` / 引理 `μ_pullback_left_snd'`

English:
lemma μ_pullback_left_snd'
  given: (g₁ : Y ⟶ X) (g₂ : Z ⟶ X)
  proof: μ_pullback_left_snd ..

@[simp]

中文:
引理 μ_pullback_left_snd'
  条件: (g₁ : Y ⟶ X) (g₂ : Z ⟶ X)
  证明: μ_pullback_left_snd ..

@[simp]
-/
lemma μ_pullback_left_snd' (g₁ : Y ⟶ X) (g₂ : Z ⟶ X) :
    (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).left ≫
      pullback.snd (pullback.fst g₁ g₂ ≫ g₁) f =
        pullback.snd _ _ ≫ pullback.snd _ _ := μ_pullback_left_snd ..

@[simp]
/--
lemma `preservesTerminalIso_pullback` / 引理 `preservesTerminalIso_pullback`

English:
lemma preservesTerminalIso_pullback
  given: (f : R ⟶ S)
  proof: by
  ext1; exact toUnit_unique _ _

中文:
引理 preservesTerminalIso_pullback
  条件: (f : R ⟶ S)
  证明: by
  ext1; exact toUnit_unique _ _

Depends on / 依赖: toUnit_unique
-/
lemma preservesTerminalIso_pullback (f : R ⟶ S) :
    preservesTerminalIso (Over.pullback f) =
      Over.isoMk (asIso (pullback.snd (𝟙 _) f)) (by simp) := by
  ext1; exact toUnit_unique _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `prodComparisonIso_pullback_inv_left_fst_fst` / 引理 `prodComparisonIso_pullback_inv_left_fst_fst`

English:
lemma prodComparisonIso_pullback_inv_left_fst_fst
  given: (f : X ⟶ Y) (A B : Over Y)
  proof: by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) A B).hom.left]; rw [Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison, fst]

@[simp]

中文:
引理 prodComparisonIso_pullback_inv_left_fst_fst
  条件: (f : X ⟶ Y) (A B : Over Y)
  证明: by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) A B).hom.left]; rw [Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison, fst]

@[simp]

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.prodComparison, Over.hom_left_inv_left_assoc, Over.pullback, cancel_epi, hom.left, hom_left_inv_left_assoc, prodComparison, prodComparisonIso, pullback
-/
lemma prodComparisonIso_pullback_inv_left_fst_fst (f : X ⟶ Y) (A B : Over Y) :
    (prodComparisonIso (Over.pullback f) A B).inv.left ≫
      pullback.fst (pullback.fst A.hom B.hom ≫ A.hom) f ≫ pullback.fst _ _ =
        pullback.fst (pullback.snd A.hom f) (pullback.snd B.hom f) ≫ pullback.fst _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) A B).hom.left]; rw [Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison, fst]

@[simp]
/--
lemma `prodComparisonIso_pullback_Spec_inv_left_fst_fst'` / 引理 `prodComparisonIso_pullback_Spec_inv_left_fst_fst'`

English:
lemma prodComparisonIso_pullback_Spec_inv_left_fst_fst'
  given: (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y)
  proof: prodComparisonIso_pullback_inv_left_fst_fst ..

中文:
引理 prodComparisonIso_pullback_Spec_inv_left_fst_fst'
  条件: (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y)
  证明: prodComparisonIso_pullback_inv_left_fst_fst ..

Depends on / 依赖: prodComparisonIso_pullback_inv_left_fst_fst
-/
lemma prodComparisonIso_pullback_Spec_inv_left_fst_fst' (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y) :
    (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫
      pullback.fst (pullback.fst gA gB ≫ gA) f ≫ pullback.fst _ _ =
        pullback.fst (pullback.snd gA f) (pullback.snd gB f) ≫ pullback.fst _ _ :=
  prodComparisonIso_pullback_inv_left_fst_fst ..

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `prodComparisonIso_pullback_inv_left_fst_snd'` / 引理 `prodComparisonIso_pullback_inv_left_fst_snd'`

English:
lemma prodComparisonIso_pullback_inv_left_fst_snd'
  given: (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y)
  proof: by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) _ _).hom.left]; rw [Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison, snd]

中文:
引理 prodComparisonIso_pullback_inv_left_fst_snd'
  条件: (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y)
  证明: by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) _ _).hom.left]; rw [Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison, snd]

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.prodComparison, Over.hom_left_inv_left_assoc, Over.pullback, cancel_epi, hom.left, hom_left_inv_left_assoc, prodComparison, prodComparisonIso, pullback
-/
lemma prodComparisonIso_pullback_inv_left_fst_snd' (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y) :
    (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫
      pullback.fst (pullback.fst gA gB ≫ gA) f ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ pullback.fst _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) _ _).hom.left]; rw [Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison, snd]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `prodComparisonIso_pullback_inv_left_snd'` / 引理 `prodComparisonIso_pullback_inv_left_snd'`

English:
lemma prodComparisonIso_pullback_inv_left_snd'
  given: (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y)
  proof: by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) _ _).hom.left]; rw [Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison]

中文:
引理 prodComparisonIso_pullback_inv_left_snd'
  条件: (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y)
  证明: by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) _ _).hom.left]; rw [Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison]

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.prodComparison, Over.hom_left_inv_left_assoc, Over.pullback, cancel_epi, hom.left, hom_left_inv_left_assoc, prodComparison, prodComparisonIso, pullback
-/
lemma prodComparisonIso_pullback_inv_left_snd' (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y) :
    (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫
      pullback.snd (pullback.fst gA gB ≫ gA) f = pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) _ _).hom.left]; rw [Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison]

/-- The pullback of a monoid object is a monoid object. -/
@[simps! -isSimp mul one]
/--
Definition of `monObjMkPullbackSnd` / `monObjMkPullbackSnd` 的定义

English:
abbreviation monObjMkPullbackSnd
  signature: [MonObj (Over.mk f)]
  body: ((Over.pullback g).mapMon.obj <| .mk <| .mk f).mon

中文:
缩写 monObjMkPullbackSnd
  签名: [MonObj (Over.mk f)]
  定义体: ((Over.pullback g).mapMon.obj <| .mk <| .mk f).mon

Depends on / 依赖: Over.pullback, mapMon, mapMon.obj, pullback
-/
abbrev monObjMkPullbackSnd [MonObj (Over.mk f)] : MonObj (Over.mk <| pullback.snd f g) :=
  ((Over.pullback g).mapMon.obj <| .mk <| .mk f).mon

attribute [local instance] monObjMkPullbackSnd

/--
Instance `isCommMonObj_mk_pullbackSnd` / 实例 `isCommMonObj_mk_pullbackSnd`

English:
instance isCommMonObj_mk_pullbackSnd
  signature: [MonObj (Over.mk f)] [IsCommMonObj (Over.mk f)]
  body: ((Over.pullback g).mapCommMon.obj <| .mk <| .mk f).comm

中文:
实例 isCommMonObj_mk_pullbackSnd
  签名: [MonObj (Over.mk f)] [是交换MonObj (Over.mk f)]
  定义体: ((Over.pullback g).mapCommMon.obj <| .mk <| .mk f).comm

Depends on / 依赖: Over.pullback, mapCommMon, mapCommMon.obj, pullback
-/
instance isCommMonObj_mk_pullbackSnd [MonObj (Over.mk f)] [IsCommMonObj (Over.mk f)] :
    IsCommMonObj (Over.mk <| pullback.snd f g) :=
  ((Over.pullback g).mapCommMon.obj <| .mk <| .mk f).comm

/-- The pullback of a monoid object is a monoid object. -/
@[simps! -isSimp mul one]
/--
Definition of `grpObjMkPullbackSnd` / `grpObjMkPullbackSnd` 的定义

English:
abbreviation grpObjMkPullbackSnd
  signature: [GrpObj (Over.mk f)]
  body: ((Over.pullback g).mapGrp.obj <| .mk <| .mk f).grp

中文:
缩写 grpObjMkPullbackSnd
  签名: [GrpObj (Over.mk f)]
  定义体: ((Over.pullback g).mapGrp.obj <| .mk <| .mk f).grp

Depends on / 依赖: Over.pullback, mapGrp, mapGrp.obj, pullback
-/
abbrev grpObjMkPullbackSnd [GrpObj (Over.mk f)] : GrpObj (Over.mk (pullback.snd f g)) :=
  ((Over.pullback g).mapGrp.obj <| .mk <| .mk f).grp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] monObjMkPullbackSnd_one in
/--
Instance `isMonHom_pullbackFst_id_right` / 实例 `isMonHom_pullbackFst_id_right`

English:
instance isMonHom_pullbackFst_id_right
  signature: [MonObj (Over.mk f)]
  body: by
    ext
    dsimp [monObjMkPullbackSnd_mul]
    simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    simp only [← Category.assoc]
    congr 1
    ext <;> simp

中文:
实例 isMonHom_pullbackFst_id_right
  签名: [MonObj (Over.mk f)]
  定义体: by
    ext
    dsimp [monObjMkPullbackSnd_mul]
    simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    simp only [← Category.assoc]
    congr 1
    ext <;> simp

Depends on / 依赖: Over.mk, pullback, pullback.snd
-/
instance isMonHom_pullbackFst_id_right [MonObj (Over.mk f)] :
IsMonHom Over.homMk (U := Over.mk <| pullback.snd f (𝟙 X)) (V := Over.mk f)
      (pullback.fst f (𝟙 X)) (pullback.condition.trans <| by simp) where
  mul_hom := by
    ext
    dsimp [monObjMkPullbackSnd_mul]
    simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    simp only [← Category.assoc]
    congr 1
    ext <;> simp

end CategoryTheory.Over
