/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Left derived functors

In this file, given a functor `F : C ⥤ H`, and `L : C ⥤ D` that is a
localization functor for `W : MorphismProperty C`, we define
`F.totalLeftDerived L W : D ⥤ H` as the right Kan extension of `F`
along `L`: it is defined if the type class `F.HasLeftDerivedFunctor W`
asserting the existence of a right Kan extension is satisfied.
(The name `totalLeftDerived` is to avoid name-collision with
`Functor.leftDerived` which are the left derived functors in
the context of abelian categories.)

Given `LF : D ⥤ H` and `α : L ⋙ LF ⟶ F`, we also introduce a type class
`F.IsLeftDerivedFunctor α W` saying that `α` is a right Kan extension of `F`
along the localization functor `L`.

(This file was obtained by dualizing the results in the file
`Mathlib.CategoryTheory.Functor.Derived.RightDerived`.)

## References

* https://ncatlab.org/nlab/show/derived+functor

-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C C' D D' H H' : Type _} [Category* C] [Category* C']
  [Category* D] [Category* D'] [Category* H] [Category* H']
  (LF'' LF' LF : D ⥤ H) {F F' F'' : C ⥤ H} (e : F ≅ F') {L : C ⥤ D}
  (α'' : L ⋙ LF'' ⟶ F'') (α' : L ⋙ LF' ⟶ F') (α : L ⋙ LF ⟶ F) (α'₂ : L ⋙ LF' ⟶ F)
  (W : MorphismProperty C)

/--
Definition of `IsLeftDerivedFunctor` / `IsLeftDerivedFunctor` 的定义

English:
class IsLeftDerivedFunctor
  parameters: (LF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D} (α : L ⋙ LF ⟶ F)
  axioms and operations (1):
    - isRightKanExtension((LF α)) : LF.IsRightKanExtension α

中文:
类 是左导出函子
  参数: (LF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D} (α : L ⋙ LF ⟶ F)
  公理与运算 (1 个):
    - isRightKanExtension((LF α)) : LF.是RightKanExtension α
-/
class IsLeftDerivedFunctor (LF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D} (α : L ⋙ LF ⟶ F)
    (W : MorphismProperty C) [L.IsLocalization W] : Prop where
  isRightKanExtension (LF α) : LF.IsRightKanExtension α

/--
lemma `isLeftDerivedFunctor_iff_isRightKanExtension` / 引理 `isLeftDerivedFunctor_iff_isRightKanExtension`

English:
lemma isLeftDerivedFunctor_iff_isRightKanExtension
  given: [L.IsLocalization W]
  proof: by
  constructor
  · exact fun _ => IsLeftDerivedFunctor.isRightKanExtension LF α W
  · exact fun h => ⟨h⟩

中文:
引理 isLeftDerivedFunctor_iff_isRightKanExtension
  条件: [L.是Localization W]
  证明: by
  constructor
  · exact fun _ => IsLeftDerivedFunctor.isRightKanExtension LF α W
  · exact fun h => ⟨h⟩

Depends on / 依赖: IsLeftDerivedFunctor, IsLeftDerivedFunctor.isRightKanExtension, isRightKanExtension
-/
lemma isLeftDerivedFunctor_iff_isRightKanExtension [L.IsLocalization W] :
    LF.IsLeftDerivedFunctor α W ↔ LF.IsRightKanExtension α := by
  constructor
  · exact fun _ => IsLeftDerivedFunctor.isRightKanExtension LF α W
  · exact fun h => ⟨h⟩

variable {RF RF'} in
/--
lemma `isLeftDerivedFunctor_iff_of_iso` / 引理 `isLeftDerivedFunctor_iff_of_iso`

English:
lemma isLeftDerivedFunctor_iff_of_iso
  statement: (α' : L ⋙ LF' ⟶ F) (W : MorphismProperty C)
  proof: by
  simp only [isLeftDerivedFunctor_iff_isRightKanExtension]
  exact isRightKanExtension_iff_of_iso e _ _ comm

中文:
引理 isLeftDerivedFunctor_iff_of_iso
  结论: (α' : L ⋙ LF' ⟶ F) (W : MorphismProperty C)
  证明: by
  simp only [isLeftDerivedFunctor_iff_isRightKanExtension]
  exact isRightKanExtension_iff_of_iso e _ _ comm

Depends on / 依赖: isLeftDerivedFunctor_iff_isRightKanExtension, isRightKanExtension_iff_of_iso
-/
lemma isLeftDerivedFunctor_iff_of_iso (α' : L ⋙ LF' ⟶ F) (W : MorphismProperty C)
    [L.IsLocalization W] (e : LF ≅ LF') (comm : whiskerLeft L e.hom ≫ α' = α) :
    LF.IsLeftDerivedFunctor α W ↔ LF'.IsLeftDerivedFunctor α' W := by
  simp only [isLeftDerivedFunctor_iff_isRightKanExtension]
  exact isRightKanExtension_iff_of_iso e _ _ comm

section

variable [L.IsLocalization W] [LF.IsLeftDerivedFunctor α W]

/--
Definition of `leftDerivedLift` / `leftDerivedLift` 的定义

English:
definition leftDerivedLift
  signature: (G : D ⥤ H) (β : L ⋙ G ⟶ F)
  body: have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension α G β

@[reassoc (attr := simp)]

中文:
定义 leftDerivedLift
  签名: (G : D ⥤ H) (β : L ⋙ G ⟶ F)
  定义体: have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension α G β

@[reassoc (attr := simp)]

Depends on / 依赖: IsLeftDerivedFunctor, IsLeftDerivedFunctor.isRightKanExtension, LF.liftOfIsRightKanExtension, isRightKanExtension, liftOfIsRightKanExtension
-/
noncomputable def leftDerivedLift (G : D ⥤ H) (β : L ⋙ G ⟶ F) : G ⟶ LF :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension α G β

@[reassoc (attr := simp)]
/--
lemma `leftDerived_fac` / 引理 `leftDerived_fac`

English:
lemma leftDerived_fac
  given: (G : D ⥤ H) (β : L ⋙ G ⟶ F)
  proof: have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension_fac α G β

@[reassoc (attr := simp)]

中文:
引理 leftDerived_fac
  条件: (G : D ⥤ H) (β : L ⋙ G ⟶ F)
  证明: have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension_fac α G β

@[reassoc (attr := simp)]

Depends on / 依赖: IsLeftDerivedFunctor, IsLeftDerivedFunctor.isRightKanExtension, LF.liftOfIsRightKanExtension_fac, isRightKanExtension, liftOfIsRightKanExtension_fac
-/
lemma leftDerived_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (LF.leftDerivedLift α W G β) ≫ α = β :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension_fac α G β

@[reassoc (attr := simp)]
/--
lemma `leftDerived_fac_app` / 引理 `leftDerived_fac_app`

English:
lemma leftDerived_fac_app
  given: (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C)
  proof: have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension_fac_app α G β X

include W in

中文:
引理 leftDerived_fac_app
  条件: (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C)
  证明: have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension_fac_app α G β X

include W in

Depends on / 依赖: IsLeftDerivedFunctor, IsLeftDerivedFunctor.isRightKanExtension, LF.liftOfIsRightKanExtension_fac_app, isRightKanExtension, liftOfIsRightKanExtension_fac_app
-/
lemma leftDerived_fac_app (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C) :
    (LF.leftDerivedLift α W G β).app (L.obj X) ≫ α.app X = β.app X :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension_fac_app α G β X

include W in
/--
lemma `leftDerived_ext` / 引理 `leftDerived_ext`

English:
lemma leftDerived_ext
  statement: (G : D ⥤ H) (γ₁ γ₂ : G ⟶ LF)
  proof: have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.hom_ext_of_isRightKanExtension α γ₁ γ₂ hγ

中文:
引理 leftDerived_ext
  结论: (G : D ⥤ H) (γ₁ γ₂ : G ⟶ LF)
  证明: have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.hom_ext_of_isRightKanExtension α γ₁ γ₂ hγ

Depends on / 依赖: IsLeftDerivedFunctor, IsLeftDerivedFunctor.isRightKanExtension, LF.hom_ext_of_isRightKanExtension, hom_ext_of_isRightKanExtension, isRightKanExtension
-/
lemma leftDerived_ext (G : D ⥤ H) (γ₁ γ₂ : G ⟶ LF)
    (hγ : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂ :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.hom_ext_of_isRightKanExtension α γ₁ γ₂ hγ

/--
Definition of `leftDerivedNatTrans` / `leftDerivedNatTrans` 的定义

English:
definition leftDerivedNatTrans
  signature: (τ : F' ⟶ F)
  body: LF.leftDerivedLift α W LF' (α' ≫ τ)

@[reassoc (attr := simp)]

中文:
定义 leftDerived自然数Trans
  签名: (τ : F' ⟶ F)
  定义体: LF.leftDerivedLift α W LF' (α' ≫ τ)

@[reassoc (attr := simp)]

Depends on / 依赖: LF.leftDerivedLift, leftDerivedLift
-/
noncomputable def leftDerivedNatTrans (τ : F' ⟶ F) : LF' ⟶ LF :=
  LF.leftDerivedLift α W LF' (α' ≫ τ)

@[reassoc (attr := simp)]
/--
lemma `leftDerivedNatTrans_fac` / 引理 `leftDerivedNatTrans_fac`

English:
lemma leftDerivedNatTrans_fac
  given: (τ : F' ⟶ F)
  proof: by
  dsimp only [leftDerivedNatTrans]
  simp

@[reassoc (attr := simp)]

中文:
引理 leftDerived自然数Trans_fac
  条件: (τ : F' ⟶ F)
  证明: by
  dsimp only [leftDerivedNatTrans]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: leftDerivedNatTrans
-/
lemma leftDerivedNatTrans_fac (τ : F' ⟶ F) :
    whiskerLeft L (leftDerivedNatTrans LF' LF α' α W τ) ≫ α = α' ≫ τ := by
  dsimp only [leftDerivedNatTrans]
  simp

@[reassoc (attr := simp)]
/--
lemma `leftDerivedNatTrans_app` / 引理 `leftDerivedNatTrans_app`

English:
lemma leftDerivedNatTrans_app
  given: (τ : F' ⟶ F) (X : C)
  proof: by
  dsimp only [leftDerivedNatTrans]
  simp

@[simp]

中文:
引理 leftDerived自然数Trans_app
  条件: (τ : F' ⟶ F) (X : C)
  证明: by
  dsimp only [leftDerivedNatTrans]
  simp

@[simp]

Depends on / 依赖: leftDerivedNatTrans
-/
lemma leftDerivedNatTrans_app (τ : F' ⟶ F) (X : C) :
    (leftDerivedNatTrans LF' LF α' α W τ).app (L.obj X) ≫ α.app X =
    α'.app X ≫ τ.app X := by
  dsimp only [leftDerivedNatTrans]
  simp

@[simp]
/--
lemma `leftDerivedNatTrans_id` / 引理 `leftDerivedNatTrans_id`

English:
lemma leftDerivedNatTrans_id
  proof: leftDerived_ext LF α W _ _ _ (by simp)

中文:
引理 leftDerived自然数Trans_id
  证明: leftDerived_ext LF α W _ _ _ (by simp)

Depends on / 依赖: leftDerived_ext
-/
lemma leftDerivedNatTrans_id :
    leftDerivedNatTrans LF LF α α W (𝟙 F) = 𝟙 LF :=
  leftDerived_ext LF α W _ _ _ (by simp)

variable [LF'.IsLeftDerivedFunctor α' W]

@[reassoc (attr := simp)]
/--
lemma `leftDerivedNatTrans_comp` / 引理 `leftDerivedNatTrans_comp`

English:
lemma leftDerivedNatTrans_comp
  given: (τ' : F'' ⟶ F') (τ : F' ⟶ F)
  proof: leftDerived_ext LF α W _ _ _ (by simp)

中文:
引理 leftDerived自然数Trans_comp
  条件: (τ' : F'' ⟶ F') (τ : F' ⟶ F)
  证明: leftDerived_ext LF α W _ _ _ (by simp)

Depends on / 依赖: leftDerived_ext
-/
lemma leftDerivedNatTrans_comp (τ' : F'' ⟶ F') (τ : F' ⟶ F) :
    leftDerivedNatTrans LF'' LF' α'' α' W τ' ≫ leftDerivedNatTrans LF' LF α' α W τ =
    leftDerivedNatTrans LF'' LF α'' α W (τ' ≫ τ) :=
  leftDerived_ext LF α W _ _ _ (by simp)

/-- The natural isomorphism `LF' ≅ LF` on left derived functors that is
induced by a natural isomorphism `F' ≅ F`. -/
@[simps]
/--
Definition of `leftDerivedNatIso` / `leftDerivedNatIso` 的定义

English:
definition leftDerivedNatIso
  signature: (τ : F' ≅ F)
  body: leftDerivedNatTrans LF' LF α' α W τ.hom
  inv := leftDerivedNatTrans LF LF' α α' W τ.inv

中文:
定义 leftDerived自然数Iso
  签名: (τ : F' ≅ F)
  定义体: leftDerivedNatTrans LF' LF α' α W τ.hom
  inv := leftDerivedNatTrans LF LF' α α' W τ.inv

Depends on / 依赖: HasFiniteLimits, hasLimitsOfShape_of_hasFiniteLimits, leftDerivedNatTrans
-/
noncomputable def leftDerivedNatIso (τ : F' ≅ F) :
    LF' ≅ LF where
  hom := leftDerivedNatTrans LF' LF α' α W τ.hom
  inv := leftDerivedNatTrans LF LF' α α' W τ.inv

/--
Definition of `leftDerivedUnique` / `leftDerivedUnique` 的定义

English:
abbreviation leftDerivedUnique
  signature: [LF'.IsLeftDerivedFunctor α'₂ W]
  body: leftDerivedNatIso LF LF' α α'₂ W (Iso.refl F)

中文:
缩写 leftDerivedUnique
  签名: [LF'.是左导出函子 α'₂ W]
  定义体: leftDerivedNatIso LF LF' α α'₂ W (Iso.refl F)

Depends on / 依赖: Iso.refl, leftDerivedNatIso
-/
noncomputable abbrev leftDerivedUnique [LF'.IsLeftDerivedFunctor α'₂ W] : LF ≅ LF' :=
  leftDerivedNatIso LF LF' α α'₂ W (Iso.refl F)

/--
lemma `isLeftDerivedFunctor_iff_isIso_leftDerivedLift` / 引理 `isLeftDerivedFunctor_iff_isIso_leftDerivedLift`

English:
lemma isLeftDerivedFunctor_iff_isIso_leftDerivedLift
  given: (G : D ⥤ H) (β : L ⋙ G ⟶ F)
  proof: by
  rw [isLeftDerivedFunctor_iff_isRightKanExtension]
  have := IsLeftDerivedFunctor.isRightKanExtension _ α W
  exact isRightKanExtension_iff_isIso _ α _ (by simp)

中文:
引理 isLeftDerivedFunctor_iff_isIso_leftDerivedLift
  条件: (G : D ⥤ H) (β : L ⋙ G ⟶ F)
  证明: by
  rw [isLeftDerivedFunctor_iff_isRightKanExtension]
  have := IsLeftDerivedFunctor.isRightKanExtension _ α W
  exact isRightKanExtension_iff_isIso _ α _ (by simp)

Depends on / 依赖: HasFiniteLimits, HasLimits, IsLeftDerivedFunctor, IsLeftDerivedFunctor.isRightKanExtension, hasFiniteLimits_of_hasLimits, isLeftDerivedFunctor_iff_isRightKanExtension, isRightKanExtension, isRightKanExtension_iff_isIso
-/
lemma isLeftDerivedFunctor_iff_isIso_leftDerivedLift (G : D ⥤ H) (β : L ⋙ G ⟶ F) :
    G.IsLeftDerivedFunctor β W ↔ IsIso (LF.leftDerivedLift α W G β) := by
  rw [isLeftDerivedFunctor_iff_isRightKanExtension]
  have := IsLeftDerivedFunctor.isRightKanExtension _ α W
  exact isRightKanExtension_iff_isIso _ α _ (by simp)

end

variable (F)

/--
Definition of `HasLeftDerivedFunctor` / `HasLeftDerivedFunctor` 的定义

English:
class HasLeftDerivedFunctor
  parameters: : Prop where
  axioms and operations (1):
    - hasRightKanExtension' : HasRightKanExtension W.Q F

中文:
类 有左导出函子
  参数: : 命题 where
  公理与运算 (1 个):
    - hasRightKanExtension' : HasRightKanExtension W.Q F

Depends on / 依赖: HasLimitsOfSize
-/
class HasLeftDerivedFunctor : Prop where
  hasRightKanExtension' : HasRightKanExtension W.Q F

variable (L)
variable [L.IsLocalization W]

/--
lemma `hasLeftDerivedFunctor_iff` / 引理 `hasLeftDerivedFunctor_iff`

English:
lemma hasLeftDerivedFunctor_iff
  proof: by
  have : HasLeftDerivedFunctor F W ↔ HasRightKanExtension W.Q F :=
    ⟨fun h => h.hasRightKanExtension', fun h => ⟨h⟩⟩
  rw [this]; rw [hasRightExtension_iff_postcomp₁ (Localization.compUniqFunctor W.Q L W) F]

中文:
引理 hasLeftDerivedFunctor_iff
  证明: by
  have : HasLeftDerivedFunctor F W ↔ HasRightKanExtension W.Q F :=
    ⟨fun h => h.hasRightKanExtension', fun h => ⟨h⟩⟩
  rw [this]; rw [hasRightExtension_iff_postcomp₁ (Localization.compUniqFunctor W.Q L W) F]

Depends on / 依赖: HasLeftDerivedFunctor, HasRightKanExtension, Localization, Localization.compUniqFunctor, ULiftHom, ULiftHom.category, category, compUniqFunctor, h.hasRightKanExtension, hasRightKanExtension, uliftCategory
-/
lemma hasLeftDerivedFunctor_iff :
    F.HasLeftDerivedFunctor W ↔ HasRightKanExtension L F := by
  have : HasLeftDerivedFunctor F W ↔ HasRightKanExtension W.Q F :=
    ⟨fun h => h.hasRightKanExtension', fun h => ⟨h⟩⟩
  rw [this]; rw [hasRightExtension_iff_postcomp₁ (Localization.compUniqFunctor W.Q L W) F]

variable {F}

include e in
/--
lemma `hasLeftDerivedFunctor_iff_of_iso` / 引理 `hasLeftDerivedFunctor_iff_of_iso`

English:
lemma hasLeftDerivedFunctor_iff_of_iso
  proof: by
  rw [hasLeftDerivedFunctor_iff F W.Q W]; rw [hasLeftDerivedFunctor_iff F' W.Q W]; rw [hasRightExtension_iff_of_iso₂ W.Q e]

中文:
引理 hasLeftDerivedFunctor_iff_of_iso
  证明: by
  rw [hasLeftDerivedFunctor_iff F W.Q W]; rw [hasLeftDerivedFunctor_iff F' W.Q W]; rw [hasRightExtension_iff_of_iso₂ W.Q e]

Depends on / 依赖: hasLeftDerivedFunctor_iff
-/
lemma hasLeftDerivedFunctor_iff_of_iso :
    HasLeftDerivedFunctor F W ↔ HasLeftDerivedFunctor F' W := by
  rw [hasLeftDerivedFunctor_iff F W.Q W]; rw [hasLeftDerivedFunctor_iff F' W.Q W]; rw [hasRightExtension_iff_of_iso₂ W.Q e]

variable (F)

/--
lemma `HasLeftDerivedFunctor.hasRightKanExtension` / 引理 `HasLeftDerivedFunctor.hasRightKanExtension`

English:
lemma HasLeftDerivedFunctor.hasRightKanExtension
  given: [HasLeftDerivedFunctor F W]
  proof: by
  simpa only [← hasLeftDerivedFunctor_iff F L W]

中文:
引理 有左导出函子.hasRightKanExtension
  条件: [有左导出函子 F W]
  证明: by
  simpa only [← hasLeftDerivedFunctor_iff F L W]

Depends on / 依赖: HasFiniteColimits, hasColimitsOfShape_of_hasFiniteColimits, hasLeftDerivedFunctor_iff
-/
lemma HasLeftDerivedFunctor.hasRightKanExtension [HasLeftDerivedFunctor F W] :
    HasRightKanExtension L F := by
  simpa only [← hasLeftDerivedFunctor_iff F L W]

variable {F L W}

/--
lemma `HasLeftDerivedFunctor.mk'` / 引理 `HasLeftDerivedFunctor.mk'`

English:
lemma HasLeftDerivedFunctor.mk'
  given: [LF.IsLeftDerivedFunctor α W]
  proof: by
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  simpa only [hasLeftDerivedFunctor_iff F L W] using HasRightKanExtension.mk LF α

中文:
引理 有左导出函子.mk'
  条件: [LF.是左导出函子 α W]
  证明: by
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  simpa only [hasLeftDerivedFunctor_iff F L W] using HasRightKanExtension.mk LF α

Depends on / 依赖: HasRightKanExtension, HasRightKanExtension.mk, IsLeftDerivedFunctor, IsLeftDerivedFunctor.isRightKanExtension, hasLeftDerivedFunctor_iff, isRightKanExtension
-/
lemma HasLeftDerivedFunctor.mk' [LF.IsLeftDerivedFunctor α W] :
    HasLeftDerivedFunctor F W := by
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  simpa only [hasLeftDerivedFunctor_iff F L W] using HasRightKanExtension.mk LF α

section

variable (F) [F.HasLeftDerivedFunctor W] (L W)

/--
Definition of `totalLeftDerived` / `totalLeftDerived` 的定义

English:
definition totalLeftDerived
  signature: : D ⥤ H
  body: have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtension L F

中文:
定义 totalLeftDerived
  签名: : D ⥤ H
  定义体: have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtension L F

Depends on / 依赖: HasColimits, HasFiniteColimits, HasLeftDerivedFunctor, HasLeftDerivedFunctor.hasRightKanExtension, hasFiniteColimits_of_hasColimits, hasRightKanExtension, rightKanExtension
-/
noncomputable def totalLeftDerived : D ⥤ H :=
  have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtension L F

/--
Definition of `totalLeftDerivedCounit` / `totalLeftDerivedCounit` 的定义

English:
definition totalLeftDerivedCounit
  signature: : L ⋙ F.totalLeftDerived L W ⟶ F
  body: have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtensionCounit L F

中文:
定义 totalLeftDerivedCounit
  签名: : L ⋙ F.totalLeftDerived L W ⟶ F
  定义体: have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtensionCounit L F

Depends on / 依赖: HasColimitsOfSize, HasLeftDerivedFunctor, HasLeftDerivedFunctor.hasRightKanExtension, hasRightKanExtension, rightKanExtensionCounit
-/
noncomputable def totalLeftDerivedCounit : L ⋙ F.totalLeftDerived L W ⟶ F :=
  have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtensionCounit L F

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (F.totalLeftDerived L W).IsLeftDerivedFunctor
  body: by
    dsimp [totalLeftDerived, totalLeftDerivedCounit]
    infer_instance

中文:
实例 :
  签名: (F.totalLeftDerived L W).是左导出函子
  定义体: by
    dsimp [totalLeftDerived, totalLeftDerivedCounit]
    infer_instance

Depends on / 依赖: infer_instance, totalLeftDerived, totalLeftDerivedCounit
-/
instance : (F.totalLeftDerived L W).IsLeftDerivedFunctor
    (F.totalLeftDerivedCounit L W) W where
  isRightKanExtension := by
    dsimp [totalLeftDerived, totalLeftDerivedCounit]
    infer_instance

end

end Functor

end CategoryTheory
