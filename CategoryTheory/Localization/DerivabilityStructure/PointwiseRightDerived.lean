/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Existence of pointwise right derived functors via derivability structures

In this file, we show how a right derivability structure can be used in
order to construct (pointwise) right derived functors.
Let `Φ` be a right derivability structure from `W₁ : MorphismProperty C₁`
to `W₂ : MorphismProperty C₂`. Let `F : C₂ ⥤ H` be a functor.
Then, the lemma `hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure`
says that `F` has a pointwise right derived functor with respect to `W₂`
if and only if `Φ.functor ⋙ F` has a pointwise right derived functor
with respect to `W₁`. This is essentially the Proposition 5.5 from the article
*Structures de dérivabilité* by Bruno Kahn and Georges Maltsiniotis (there,
it was stated in terms of absolute derived functors).

In particular, if `Φ.functor ⋙ F` inverts `W₁`, it follows that the
right derived functor of `F` with respect to `W₂` exists.

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Limits Category CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H]
  {D₁ : Type u₄} {D₂ : Type u₅}
  [Category.{v₄} D₁] [Category.{v₅} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂) (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  (F : C₂ ⥤ H) (F₁ : D₁ ⥤ H) (α₁ : Φ.functor ⋙ F ⟶ L₁ ⋙ F₁)
  (F₂ : D₂ ⥤ H) (α₂ : F ⟶ L₂ ⋙ F₂)
  [F₁.IsRightDerivedFunctor α₁ W₁]

/-- If `Φ` is a localizer morphism from `W₁ : MorphismProperty C₁` to
`W₂ : MorphismProperty C₂`, if `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are
localization functors for `W₁` and `W₂`, if `F : C₂ ⥤ H` is a functor,
if `F₁ : D₁ ⥤ H` is a right derived functor of `Φ.functor ⋙ F`,
and if `F₂ : D₂ ⥤ H` is a functor equipped with a
natural transformation `α₂ : F ⟶ L₂ ⋙ F₂`, this is the canonical
morphism `F₁ ⟶ Φ.localizedFunctor L₁ L₂ ⋙ F₂`. -/
/-
**CategoryTheory.LocalizerMorphism.rightDerivedFunctorComparison** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：rightDerivedFunctorComparison : F₁ ⟶ Φ.localizedFunctor L₁ L₂ ⋙ F₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Φ` is a localizer morphism from `W₁ : MorphismProperty C₁` to
`W₂ : MorphismProperty C₂`, if `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are
localization functors for `W₁` and `W₂`, if `F : C₂ ⥤ H` is a functor,
if `F₁ : D₁ ⥤ H` is a right derived functor of `Φ.functor ⋙ F`,
and if `F₂ : D₂ ⥤ H` is a functor equipped with a
natural transformation `α₂ : F ⟶ L₂ ⋙ F₂`, this is the canonical
morphism `F₁ ⟶ Φ.localizedFunctor L₁ L₂ ⋙ F₂`.
-/
noncomputable def rightDerivedFunctorComparison :
    F₁ ⟶ Φ.localizedFunctor L₁ L₂ ⋙ F₂ :=
  F₁.rightDerivedDesc α₁ W₁ (Φ.localizedFunctor L₁ L₂ ⋙ F₂)
    (whiskerLeft _ α₂ ≫ (Functor.associator _ _ _).inv ≫
      whiskerRight ((Φ.catCommSq L₁ L₂).iso).hom F₂ ≫ (Functor.associator _ _ _).hom)

@[reassoc]
/-
**CategoryTheory.LocalizerMorphism.rightDerivedFunctorComparison_fac** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：rightDerivedFunctorComparison_fac : α₁ ≫ whiskerLeft _ (Φ.rightDerivedFunc
torComparison L₁ L₂ F F₁ α₁ F₂ α₂) = whiskerLeft Φ.functor α₂ ≫ ((Functor.associ
ator _ _ _).inv ≫ whiskerRight ((Φ.catCommSq L₁ L₂).iso).hom F₂ ≫ (Functor.assoc
iator _ _ _).hom)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.rightDerived_fac`：rightDerived_fac (G : D ⥤ H) (β
 : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (RF.rightDerivedDesc α W G β) = β
-/
lemma rightDerivedFunctorComparison_fac :
    α₁ ≫ whiskerLeft _ (Φ.rightDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂) =
      whiskerLeft Φ.functor α₂ ≫ ((Functor.associator _ _ _).inv ≫
      whiskerRight ((Φ.catCommSq L₁ L₂).iso).hom F₂ ≫ (Functor.associator _ _ _).hom) := by
  dsimp only [rightDerivedFunctorComparison]
  rw [Functor.rightDerived_fac]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.LocalizerMorphism.rightDerivedFunctorComparison_fac_app** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：rightDerivedFunctorComparison_fac_app (X : C₁) : α₁.app X ≫ (Φ.rightDerive
dFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂).app (L₁.obj X) = α₂.app (Φ.functor.obj X
) ≫ F₂.map (((Φ.catCommSq L₁ L₂).iso).hom.app X)
参数：X : C₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.LocalizerMorphism.rightDerivedFunctorComparison_fac`：righ
tDerivedFunctorComparison_fac : α₁ ≫ whiskerLeft _ (Φ.rightDerivedFunctorCompari
son L₁ L₂ F F₁ α₁ F₂ α₂) = whiskerLeft Φ.functor α₂ ≫ ((…
-/
lemma rightDerivedFunctorComparison_fac_app (X : C₁) :
    α₁.app X ≫ (Φ.rightDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂).app (L₁.obj X) =
      α₂.app (Φ.functor.obj X) ≫ F₂.map (((Φ.catCommSq L₁ L₂).iso).hom.app X) := by
  simpa using congr_app (Φ.rightDerivedFunctorComparison_fac L₁ L₂ F F₁ α₁ F₂ α₂) X

variable [Φ.IsRightDerivabilityStructure]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.LocalizerMorphism.hasPointwiseRightDerivedFunctorAt_iff_of_isRi
ghtDerivabilityStructure** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorp
hism`。
形式化陈述：hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure (X :
 C₁) : (Φ.functor ⋙ F).HasPointwiseRightDerivedFunctorAt W₁ X ↔ F.HasPointwiseRi
ghtDerivedFunctorAt W₂ (Φ.functor.obj X)
参数：X : C₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightDerivedFunctorAt_iff`：hasPointwi
seRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) : F.HasPointwiseRightDe
rivedFunctorAt W X ↔ HasPointwiseLeftKanExtensionA…
· 使用引理 `CategoryTheory.TwoSquare.hasPointwiseLeftKanExtensionAt_iff`：hasPointwis
eLeftKanExtensionAt_iff (F : C₂ ⥤ D) (X₃ : C₃) [(w.costructuredArrowRightwards X
₃).Final] : L.HasPointwiseLeftKanExtensionAt (T ⋙…
· 使用定理 `CategoryTheory.TwoSquare.instFinalCostructuredArrowObjCostructuredArrowR
ightwardsOfGuitartExact`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Ty
pe u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.C
atego…
· 使用定理 `CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure.guitartExa
ct'`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} C₁
}   {inst_1 : CategoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用引理 `CategoryTheory.Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso`：hasPoi
ntwiseLeftKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) : HasPointwiseLeft
KanExtensionAt L F Y₁ ↔ HasPointwiseLeftKanExtensionAt…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure (X : C₁) :
    (Φ.functor ⋙ F).HasPointwiseRightDerivedFunctorAt W₁ X ↔
      F.HasPointwiseRightDerivedFunctorAt W₂ (Φ.functor.obj X) := by
  let e : W₂.Q.obj _ ≅ (Φ.localizedFunctor W₁.Q W₂.Q).obj _ := ((Φ.catCommSq W₁.Q W₂.Q).iso).app X
  rw [F.hasPointwiseRightDerivedFunctorAt_iff W₂.Q W₂ (Φ.functor.obj X),
    (Φ.functor ⋙ F).hasPointwiseRightDerivedFunctorAt_iff W₁.Q W₁ X,
    TwoSquare.hasPointwiseLeftKanExtensionAt_iff ((Φ.catCommSq W₁.Q W₂.Q).iso).hom,
    Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso W₂.Q F e]
/-
**CategoryTheory.LocalizerMorphism.hasPointwiseRightDerivedFunctor_iff_of_isRigh
tDerivabilityStructure** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphi
sm`。
形式化陈述：hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure : F.Ha
sPointwiseRightDerivedFunctor W₂ ↔ ((Φ.functor ⋙ F).HasPointwiseRightDerivedFunc
tor W₁)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.hasPointwiseRightDerivedFunctorAt_iff_o
f_isRightDerivabilityStructure`：hasPointwiseRightDerivedFunctorAt_iff_of_isRight
DerivabilityStructure (X : C₁) : (Φ.functor ⋙ F).HasPointwiseRightDerivedFunctor
At W₁ X ↔ F.…
· 使用定理 `CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure.hasRightRe
solutions`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, 
u₁} C₁}   {inst_1 : CategoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`：has
PointwiseRightDerivedFunctorAt_iff_of_mem {X Y : C} (w : X ⟶ Y) (hw : W w) : F.H
asPointwiseRightDerivedFunctorAt W X ↔ F.HasPointwiseRigh…
· 使用定理 `CategoryTheory.LocalizerMorphism.RightResolution.hw`：∀ {C₁ : Type u_1} {
C₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
-/
lemma hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure :
    F.HasPointwiseRightDerivedFunctor W₂ ↔
      ((Φ.functor ⋙ F).HasPointwiseRightDerivedFunctor W₁) := by
  constructor
  · intro hF X₁
    rw [hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure]
    apply hF
  · intro hF X₂
    have R : Φ.RightResolution X₂ := Classical.arbitrary _
    simpa only [hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure,
      ← F.hasPointwiseRightDerivedFunctorAt_iff_of_mem W₂ R.w R.hw] using hF R.X₁

section

variable [(Φ.functor ⋙ F).HasPointwiseRightDerivedFunctor W₁]
  [F₂.IsRightDerivedFunctor α₂ W₂]

/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (Φ.rightDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂) := by
  have : F.HasPointwiseRightDerivedFunctor W₂ := by
    rw [Φ.hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure]
    infer_instance
  dsimp only [rightDerivedFunctorComparison]
  rw [← isRightDerivedFunctor_iff_isIso_rightDerivedDesc,
    isRightDerivedFunctor_iff_isLeftKanExtension]
  exact ((F₂.isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor α₂ W₂).compTwoSquare
    ((Φ.catCommSq L₁ L₂).iso).hom).isLeftKanExtension
/-
**CategoryTheory.LocalizerMorphism.isIso_iff_of_isRightDerivabilityStructure** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isIso_iff_of_isRightDerivabilityStructure (X : C₁) : IsIso (α₁.app X) ↔ Is
Iso (α₂.app (Φ.functor.obj X))
参数：X : C₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.isIso_comp_right_iff`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X) [CategoryTheory.IsIso 
f],   CategoryTheory.IsIs…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.LocalizerMorphism.instIsIsoFunctorRightDerivedFunctorComp
arison`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] …
· 使用引理 `CategoryTheory.LocalizerMorphism.rightDerivedFunctorComparison_fac_app`：
rightDerivedFunctorComparison_fac_app (X : C₁) : α₁.app X ≫ (Φ.rightDerivedFunct
orComparison L₁ L₂ F F₁ α₁ F₂ α₂).app (L₁.obj X) = α₂.app (Φ…
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isIso_iff_of_isRightDerivabilityStructure (X : C₁) :
    IsIso (α₁.app X) ↔ IsIso (α₂.app (Φ.functor.obj X)) := by
  rw [← isIso_comp_right_iff (α₁.app X)
    ((Φ.rightDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂).app (L₁.obj X)),
    rightDerivedFunctorComparison_fac_app, isIso_comp_right_iff]

end

end LocalizerMorphism

end CategoryTheory

