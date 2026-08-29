/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Right derived functors

In this file, given a functor `F : C ⥤ H`, and `L : C ⥤ D` that is a
localization functor for `W : MorphismProperty C`, we define
`F.totalRightDerived L W : D ⥤ H` as the left Kan extension of `F`
along `L`: it is defined if the type class `F.HasRightDerivedFunctor W`
asserting the existence of a left Kan extension is satisfied.
(The name `totalRightDerived` is to avoid name-collision with
`Functor.rightDerived` which are the right derived functors in
the context of abelian categories.)

Given `RF : D ⥤ H` and `α : F ⟶ L ⋙ RF`, we also introduce a type class
`F.IsRightDerivedFunctor α W` saying that `α` is a left Kan extension of `F`
along the localization functor `L`.

## TODO

- refactor `Functor.rightDerived` (and `Functor.leftDerived`) when the necessary
  material enters mathlib: derived categories, injective/projective derivability
  structures, existence of derived functors from derivability structures.

## References

* https://ncatlab.org/nlab/show/derived+functor

-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C C' D D' H H' : Type _} [Category* C] [Category* C']
  [Category* D] [Category* D'] [Category* H] [Category* H']
  (RF RF' RF'' : D ⥤ H) {F F' F'' : C ⥤ H} (e : F ≅ F') {L : C ⥤ D}
  (α : F ⟶ L ⋙ RF) (α' : F' ⟶ L ⋙ RF') (α'' : F'' ⟶ L ⋙ RF'') (α'₂ : F ⟶ L ⋙ RF')
  (W : MorphismProperty C)

/--
Definition of `IsRightDerivedFunctor` / `IsRightDerivedFunctor` 的定义

English:
class IsRightDerivedFunctor
  parameters: (RF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D} (α : F ⟶ L ⋙ RF)
  axioms and operations (1):
    - isLeftKanExtension((RF α)) : RF.IsLeftKanExtension α

中文:
类 是右导出函子
  参数: (RF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D} (α : F ⟶ L ⋙ RF)
  公理与运算 (1 个):
    - isLeftKanExtension((RF α)) : RF.是LeftKanExtension α
-/
class IsRightDerivedFunctor (RF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D} (α : F ⟶ L ⋙ RF)
    (W : MorphismProperty C) [L.IsLocalization W] : Prop where
  isLeftKanExtension (RF α) : RF.IsLeftKanExtension α

/--
lemma `isRightDerivedFunctor_iff_isLeftKanExtension` / 引理 `isRightDerivedFunctor_iff_isLeftKanExtension`

English:
lemma isRightDerivedFunctor_iff_isLeftKanExtension
  given: [L.IsLocalization W]
  proof: by
  constructor
  · exact fun _ => IsRightDerivedFunctor.isLeftKanExtension RF α W
  · exact fun h => ⟨h⟩

中文:
引理 isRightDerivedFunctor_iff_isLeftKanExtension
  条件: [L.是Localization W]
  证明: by
  constructor
  · exact fun _ => IsRightDerivedFunctor.isLeftKanExtension RF α W
  · exact fun h => ⟨h⟩

Depends on / 依赖: IsRightDerivedFunctor, IsRightDerivedFunctor.isLeftKanExtension, isLeftKanExtension
-/
lemma isRightDerivedFunctor_iff_isLeftKanExtension [L.IsLocalization W] :
    RF.IsRightDerivedFunctor α W ↔ RF.IsLeftKanExtension α := by
  constructor
  · exact fun _ => IsRightDerivedFunctor.isLeftKanExtension RF α W
  · exact fun h => ⟨h⟩

variable {RF RF'} in
/--
lemma `isRightDerivedFunctor_iff_of_iso` / 引理 `isRightDerivedFunctor_iff_of_iso`

English:
lemma isRightDerivedFunctor_iff_of_iso
  statement: (α' : F ⟶ L ⋙ RF') (W : MorphismProperty C)
  proof: by
  simp only [isRightDerivedFunctor_iff_isLeftKanExtension]
  exact isLeftKanExtension_iff_of_iso e _ _ comm

中文:
引理 isRightDerivedFunctor_iff_of_iso
  结论: (α' : F ⟶ L ⋙ RF') (W : MorphismProperty C)
  证明: by
  simp only [isRightDerivedFunctor_iff_isLeftKanExtension]
  exact isLeftKanExtension_iff_of_iso e _ _ comm

Depends on / 依赖: isLeftKanExtension_iff_of_iso, isRightDerivedFunctor_iff_isLeftKanExtension
-/
lemma isRightDerivedFunctor_iff_of_iso (α' : F ⟶ L ⋙ RF') (W : MorphismProperty C)
    [L.IsLocalization W] (e : RF ≅ RF') (comm : α ≫ whiskerLeft L e.hom = α') :
    RF.IsRightDerivedFunctor α W ↔ RF'.IsRightDerivedFunctor α' W := by
  simp only [isRightDerivedFunctor_iff_isLeftKanExtension]
  exact isLeftKanExtension_iff_of_iso e _ _ comm

section

variable [L.IsLocalization W] [RF.IsRightDerivedFunctor α W]

/--
Definition of `rightDerivedDesc` / `rightDerivedDesc` 的定义

English:
definition rightDerivedDesc
  signature: (G : D ⥤ H) (β : F ⟶ L ⋙ G)
  body: have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension α G β

@[reassoc (attr := simp)]

中文:
定义 rightDerivedDesc
  签名: (G : D ⥤ H) (β : F ⟶ L ⋙ G)
  定义体: have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension α G β

@[reassoc (attr := simp)]

Depends on / 依赖: IsRightDerivedFunctor, IsRightDerivedFunctor.isLeftKanExtension, RF.descOfIsLeftKanExtension, descOfIsLeftKanExtension, isLeftKanExtension
-/
noncomputable def rightDerivedDesc (G : D ⥤ H) (β : F ⟶ L ⋙ G) : RF ⟶ G :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension α G β

@[reassoc (attr := simp)]
/--
lemma `rightDerived_fac` / 引理 `rightDerived_fac`

English:
lemma rightDerived_fac
  given: (G : D ⥤ H) (β : F ⟶ L ⋙ G)
  proof: have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension_fac α G β

@[reassoc (attr := simp)]

中文:
引理 rightDerived_fac
  条件: (G : D ⥤ H) (β : F ⟶ L ⋙ G)
  证明: have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension_fac α G β

@[reassoc (attr := simp)]

Depends on / 依赖: IsRightDerivedFunctor, IsRightDerivedFunctor.isLeftKanExtension, RF.descOfIsLeftKanExtension_fac, descOfIsLeftKanExtension_fac, isLeftKanExtension
-/
lemma rightDerived_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    α ≫ whiskerLeft L (RF.rightDerivedDesc α W G β) = β :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension_fac α G β

@[reassoc (attr := simp)]
/--
lemma `rightDerived_fac_app` / 引理 `rightDerived_fac_app`

English:
lemma rightDerived_fac_app
  given: (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C)
  proof: have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension_fac_app α G β X

include W in

中文:
引理 rightDerived_fac_app
  条件: (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C)
  证明: have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension_fac_app α G β X

include W in

Depends on / 依赖: IsRightDerivedFunctor, IsRightDerivedFunctor.isLeftKanExtension, RF.descOfIsLeftKanExtension_fac_app, descOfIsLeftKanExtension_fac_app, isLeftKanExtension
-/
lemma rightDerived_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) :
    α.app X ≫ (RF.rightDerivedDesc α W G β).app (L.obj X) = β.app X :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension_fac_app α G β X

include W in
/--
lemma `rightDerived_ext` / 引理 `rightDerived_ext`

English:
lemma rightDerived_ext
  statement: (G : D ⥤ H) (γ₁ γ₂ : RF ⟶ G)
  proof: have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.hom_ext_of_isLeftKanExtension α γ₁ γ₂ hγ

中文:
引理 rightDerived_ext
  结论: (G : D ⥤ H) (γ₁ γ₂ : RF ⟶ G)
  证明: have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.hom_ext_of_isLeftKanExtension α γ₁ γ₂ hγ

Depends on / 依赖: IsRightDerivedFunctor, IsRightDerivedFunctor.isLeftKanExtension, RF.hom_ext_of_isLeftKanExtension, hom_ext_of_isLeftKanExtension, isLeftKanExtension
-/
lemma rightDerived_ext (G : D ⥤ H) (γ₁ γ₂ : RF ⟶ G)
    (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiskerLeft L γ₂) : γ₁ = γ₂ :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.hom_ext_of_isLeftKanExtension α γ₁ γ₂ hγ

/--
Definition of `rightDerivedNatTrans` / `rightDerivedNatTrans` 的定义

English:
definition rightDerivedNatTrans
  signature: (τ : F ⟶ F')
  body: RF.rightDerivedDesc α W RF' (τ ≫ α')

@[reassoc (attr := simp)]

中文:
定义 rightDerived自然数Trans
  签名: (τ : F ⟶ F')
  定义体: RF.rightDerivedDesc α W RF' (τ ≫ α')

@[reassoc (attr := simp)]

Depends on / 依赖: RF.rightDerivedDesc, rightDerivedDesc
-/
noncomputable def rightDerivedNatTrans (τ : F ⟶ F') : RF ⟶ RF' :=
  RF.rightDerivedDesc α W RF' (τ ≫ α')

@[reassoc (attr := simp)]
/--
lemma `rightDerivedNatTrans_fac` / 引理 `rightDerivedNatTrans_fac`

English:
lemma rightDerivedNatTrans_fac
  given: (τ : F ⟶ F')
  proof: by
  dsimp only [rightDerivedNatTrans]
  simp

@[reassoc (attr := simp)]

中文:
引理 rightDerived自然数Trans_fac
  条件: (τ : F ⟶ F')
  证明: by
  dsimp only [rightDerivedNatTrans]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: rightDerivedNatTrans
-/
lemma rightDerivedNatTrans_fac (τ : F ⟶ F') :
    α ≫ whiskerLeft L (rightDerivedNatTrans RF RF' α α' W τ) = τ ≫ α' := by
  dsimp only [rightDerivedNatTrans]
  simp

@[reassoc (attr := simp)]
/--
lemma `rightDerivedNatTrans_app` / 引理 `rightDerivedNatTrans_app`

English:
lemma rightDerivedNatTrans_app
  given: (τ : F ⟶ F') (X : C)
  proof: by
  dsimp only [rightDerivedNatTrans]
  simp

@[simp]

中文:
引理 rightDerived自然数Trans_app
  条件: (τ : F ⟶ F') (X : C)
  证明: by
  dsimp only [rightDerivedNatTrans]
  simp

@[simp]

Depends on / 依赖: rightDerivedNatTrans
-/
lemma rightDerivedNatTrans_app (τ : F ⟶ F') (X : C) :
    α.app X ≫ (rightDerivedNatTrans RF RF' α α' W τ).app (L.obj X) =
    τ.app X ≫ α'.app X := by
  dsimp only [rightDerivedNatTrans]
  simp

@[simp]
/--
lemma `rightDerivedNatTrans_id` / 引理 `rightDerivedNatTrans_id`

English:
lemma rightDerivedNatTrans_id
  proof: rightDerived_ext RF α W _ _ _ (by simp)

中文:
引理 rightDerived自然数Trans_id
  证明: rightDerived_ext RF α W _ _ _ (by simp)

Depends on / 依赖: rightDerived_ext
-/
lemma rightDerivedNatTrans_id :
    rightDerivedNatTrans RF RF α α W (𝟙 F) = 𝟙 RF :=
  rightDerived_ext RF α W _ _ _ (by simp)

variable [RF'.IsRightDerivedFunctor α' W]

@[reassoc (attr := simp)]
/--
lemma `rightDerivedNatTrans_comp` / 引理 `rightDerivedNatTrans_comp`

English:
lemma rightDerivedNatTrans_comp
  given: (τ : F ⟶ F') (τ' : F' ⟶ F'')
  proof: rightDerived_ext RF α W _ _ _ (by simp)

中文:
引理 rightDerived自然数Trans_comp
  条件: (τ : F ⟶ F') (τ' : F' ⟶ F'')
  证明: rightDerived_ext RF α W _ _ _ (by simp)

Depends on / 依赖: rightDerived_ext
-/
lemma rightDerivedNatTrans_comp (τ : F ⟶ F') (τ' : F' ⟶ F'') :
    rightDerivedNatTrans RF RF' α α' W τ ≫ rightDerivedNatTrans RF' RF'' α' α'' W τ' =
    rightDerivedNatTrans RF RF'' α α'' W (τ ≫ τ') :=
  rightDerived_ext RF α W _ _ _ (by simp)

/-- The natural isomorphism `RF ≅ RF'` on right derived functors that is
induced by a natural isomorphism `F ≅ F'`. -/
@[simps]
/--
Definition of `rightDerivedNatIso` / `rightDerivedNatIso` 的定义

English:
definition rightDerivedNatIso
  signature: (τ : F ≅ F')
  body: rightDerivedNatTrans RF RF' α α' W τ.hom
  inv := rightDerivedNatTrans RF' RF α' α W τ.inv

中文:
定义 rightDerived自然数Iso
  签名: (τ : F ≅ F')
  定义体: rightDerivedNatTrans RF RF' α α' W τ.hom
  inv := rightDerivedNatTrans RF' RF α' α W τ.inv

Depends on / 依赖: rightDerivedNatTrans
-/
noncomputable def rightDerivedNatIso (τ : F ≅ F') :
    RF ≅ RF' where
  hom := rightDerivedNatTrans RF RF' α α' W τ.hom
  inv := rightDerivedNatTrans RF' RF α' α W τ.inv

/--
Definition of `rightDerivedUnique` / `rightDerivedUnique` 的定义

English:
abbreviation rightDerivedUnique
  signature: [RF'.IsRightDerivedFunctor α'₂ W]
  body: rightDerivedNatIso RF RF' α α'₂ W (Iso.refl F)

中文:
缩写 rightDerivedUnique
  签名: [RF'.是右导出函子 α'₂ W]
  定义体: rightDerivedNatIso RF RF' α α'₂ W (Iso.refl F)

Depends on / 依赖: Iso.refl, rightDerivedNatIso
-/
noncomputable abbrev rightDerivedUnique [RF'.IsRightDerivedFunctor α'₂ W] : RF ≅ RF' :=
  rightDerivedNatIso RF RF' α α'₂ W (Iso.refl F)

/--
lemma `isRightDerivedFunctor_iff_isIso_rightDerivedDesc` / 引理 `isRightDerivedFunctor_iff_isIso_rightDerivedDesc`

English:
lemma isRightDerivedFunctor_iff_isIso_rightDerivedDesc
  given: (G : D ⥤ H) (β : F ⟶ L ⋙ G)
  proof: by
  rw [isRightDerivedFunctor_iff_isLeftKanExtension]
  have := IsRightDerivedFunctor.isLeftKanExtension _ α W
  exact isLeftKanExtension_iff_isIso _ α _ (by simp)

中文:
引理 isRightDerivedFunctor_iff_isIso_rightDerivedDesc
  条件: (G : D ⥤ H) (β : F ⟶ L ⋙ G)
  证明: by
  rw [isRightDerivedFunctor_iff_isLeftKanExtension]
  have := IsRightDerivedFunctor.isLeftKanExtension _ α W
  exact isLeftKanExtension_iff_isIso _ α _ (by simp)

Depends on / 依赖: IsRightDerivedFunctor, IsRightDerivedFunctor.isLeftKanExtension, isLeftKanExtension, isLeftKanExtension_iff_isIso, isRightDerivedFunctor_iff_isLeftKanExtension
-/
lemma isRightDerivedFunctor_iff_isIso_rightDerivedDesc (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    G.IsRightDerivedFunctor β W ↔ IsIso (RF.rightDerivedDesc α W G β) := by
  rw [isRightDerivedFunctor_iff_isLeftKanExtension]
  have := IsRightDerivedFunctor.isLeftKanExtension _ α W
  exact isLeftKanExtension_iff_isIso _ α _ (by simp)

end

variable (F)

/--
Definition of `HasRightDerivedFunctor` / `HasRightDerivedFunctor` 的定义

English:
class HasRightDerivedFunctor
  parameters: : Prop where
  axioms and operations (1):
    - hasLeftKanExtension' : HasLeftKanExtension W.Q F

中文:
类 有右导出函子
  参数: : 命题 where
  公理与运算 (1 个):
    - hasLeftKanExtension' : 有LeftKanExtension W.Q F

Depends on / 依赖: Sum.elim
-/
class HasRightDerivedFunctor : Prop where
  hasLeftKanExtension' : HasLeftKanExtension W.Q F

variable (L)
variable [L.IsLocalization W]

/--
lemma `hasRightDerivedFunctor_iff` / 引理 `hasRightDerivedFunctor_iff`

English:
lemma hasRightDerivedFunctor_iff
  proof: by
  have : HasRightDerivedFunctor F W ↔ HasLeftKanExtension W.Q F :=
    ⟨fun h => h.hasLeftKanExtension', fun h => ⟨h⟩⟩
  rw [this]; rw [hasLeftExtension_iff_postcomp₁ (Localization.compUniqFunctor W.Q L W) F]

中文:
引理 hasRightDerivedFunctor_iff
  证明: by
  have : HasRightDerivedFunctor F W ↔ HasLeftKanExtension W.Q F :=
    ⟨fun h => h.hasLeftKanExtension', fun h => ⟨h⟩⟩
  rw [this]; rw [hasLeftExtension_iff_postcomp₁ (Localization.compUniqFunctor W.Q L W) F]

Depends on / 依赖: HasLeftKanExtension, HasRightDerivedFunctor, Localization, Localization.compUniqFunctor, compUniqFunctor, h.hasLeftKanExtension, hasLeftKanExtension
-/
lemma hasRightDerivedFunctor_iff :
    F.HasRightDerivedFunctor W ↔ HasLeftKanExtension L F := by
  have : HasRightDerivedFunctor F W ↔ HasLeftKanExtension W.Q F :=
    ⟨fun h => h.hasLeftKanExtension', fun h => ⟨h⟩⟩
  rw [this]; rw [hasLeftExtension_iff_postcomp₁ (Localization.compUniqFunctor W.Q L W) F]

variable {F}

include e in
/--
lemma `hasRightDerivedFunctor_iff_of_iso` / 引理 `hasRightDerivedFunctor_iff_of_iso`

English:
lemma hasRightDerivedFunctor_iff_of_iso
  proof: by
  rw [hasRightDerivedFunctor_iff F W.Q W]; rw [hasRightDerivedFunctor_iff F' W.Q W]; rw [hasLeftExtension_iff_of_iso₂ W.Q e]

中文:
引理 hasRightDerivedFunctor_iff_of_iso
  证明: by
  rw [hasRightDerivedFunctor_iff F W.Q W]; rw [hasRightDerivedFunctor_iff F' W.Q W]; rw [hasLeftExtension_iff_of_iso₂ W.Q e]

Depends on / 依赖: hasRightDerivedFunctor_iff
-/
lemma hasRightDerivedFunctor_iff_of_iso :
    HasRightDerivedFunctor F W ↔ HasRightDerivedFunctor F' W := by
  rw [hasRightDerivedFunctor_iff F W.Q W]; rw [hasRightDerivedFunctor_iff F' W.Q W]; rw [hasLeftExtension_iff_of_iso₂ W.Q e]

variable (F)

/--
lemma `HasRightDerivedFunctor.hasLeftKanExtension` / 引理 `HasRightDerivedFunctor.hasLeftKanExtension`

English:
lemma HasRightDerivedFunctor.hasLeftKanExtension
  given: [HasRightDerivedFunctor F W]
  proof: by
  simpa only [← hasRightDerivedFunctor_iff F L W]

中文:
引理 有右导出函子.hasLeftKanExtension
  条件: [有右导出函子 F W]
  证明: by
  simpa only [← hasRightDerivedFunctor_iff F L W]

Depends on / 依赖: hasRightDerivedFunctor_iff
-/
lemma HasRightDerivedFunctor.hasLeftKanExtension [HasRightDerivedFunctor F W] :
    HasLeftKanExtension L F := by
  simpa only [← hasRightDerivedFunctor_iff F L W]

variable {F L W}

/--
lemma `HasRightDerivedFunctor.mk'` / 引理 `HasRightDerivedFunctor.mk'`

English:
lemma HasRightDerivedFunctor.mk'
  given: [RF.IsRightDerivedFunctor α W]
  proof: by
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  simpa only [hasRightDerivedFunctor_iff F L W] using HasLeftKanExtension.mk RF α

中文:
引理 有右导出函子.mk'
  条件: [RF.是右导出函子 α W]
  证明: by
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  simpa only [hasRightDerivedFunctor_iff F L W] using HasLeftKanExtension.mk RF α

Depends on / 依赖: HasLeftKanExtension, HasLeftKanExtension.mk, IsRightDerivedFunctor, IsRightDerivedFunctor.isLeftKanExtension, hasRightDerivedFunctor_iff, isLeftKanExtension
-/
lemma HasRightDerivedFunctor.mk' [RF.IsRightDerivedFunctor α W] :
    HasRightDerivedFunctor F W := by
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  simpa only [hasRightDerivedFunctor_iff F L W] using HasLeftKanExtension.mk RF α

section

variable (F) [F.HasRightDerivedFunctor W] (L W)

/--
Definition of `totalRightDerived` / `totalRightDerived` 的定义

English:
definition totalRightDerived
  signature: : D ⥤ H
  body: have := HasRightDerivedFunctor.hasLeftKanExtension F L W
  leftKanExtension L F

中文:
定义 totalRightDerived
  签名: : D ⥤ H
  定义体: have := HasRightDerivedFunctor.hasLeftKanExtension F L W
  leftKanExtension L F

Depends on / 依赖: HasRightDerivedFunctor, HasRightDerivedFunctor.hasLeftKanExtension, hasLeftKanExtension, leftKanExtension
-/
noncomputable def totalRightDerived : D ⥤ H :=
  have := HasRightDerivedFunctor.hasLeftKanExtension F L W
  leftKanExtension L F

/--
Definition of `totalRightDerivedUnit` / `totalRightDerivedUnit` 的定义

English:
definition totalRightDerivedUnit
  signature: : F ⟶ L ⋙ F.totalRightDerived L W
  body: have := HasRightDerivedFunctor.hasLeftKanExtension F L W
  leftKanExtensionUnit L F

中文:
定义 totalRightDerivedUnit
  签名: : F ⟶ L ⋙ F.totalRightDerived L W
  定义体: have := HasRightDerivedFunctor.hasLeftKanExtension F L W
  leftKanExtensionUnit L F

Depends on / 依赖: HasRightDerivedFunctor, HasRightDerivedFunctor.hasLeftKanExtension, hasLeftKanExtension, leftKanExtensionUnit
-/
noncomputable def totalRightDerivedUnit : F ⟶ L ⋙ F.totalRightDerived L W :=
  have := HasRightDerivedFunctor.hasLeftKanExtension F L W
  leftKanExtensionUnit L F

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (F.totalRightDerived L W).IsRightDerivedFunctor
  body: by
    dsimp [totalRightDerived, totalRightDerivedUnit]
    infer_instance

中文:
实例 :
  签名: (F.totalRightDerived L W).是右导出函子
  定义体: by
    dsimp [totalRightDerived, totalRightDerivedUnit]
    infer_instance

Depends on / 依赖: infer_instance, totalRightDerived, totalRightDerivedUnit
-/
instance : (F.totalRightDerived L W).IsRightDerivedFunctor
    (F.totalRightDerivedUnit L W) W where
  isLeftKanExtension := by
    dsimp [totalRightDerived, totalRightDerivedUnit]
    infer_instance

end

end Functor

end CategoryTheory
