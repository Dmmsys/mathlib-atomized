/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.PointwiseRightDerived

/-!
# Deriving functors using a derivability structure

Let `Φ : LocalizerMorphism W₁ W₂` be a localizer morphism between classes
of morphisms on categories `C₁` and `C₂`. Let `F : C₂ ⥤ H`.
When `Φ` is a left or right derivability structure, it allows to derive
the functor `F` (with respect to `W₂`) when `Φ.functor ⋙ F : C₁ ⥤ H`
inverts `W₁` (this is the most favorable case when we can apply the lemma
`hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure`).
We define `Φ.Derives F` as an abbreviation for `W₁.IsInvertedBy (Φ.functor ⋙ F)`.

When `h : Φ.Derives F` holds and `Φ` is a right derivability structure,
we show that `F` has a right derived functor with respect to `W₂`.
Under this assumption, if `L₂ : C₂ ⥤ D₂` is a localization functor
for `W₂`, then a functor `RF : D₂ ⥤ H` equipped with a natural
transformation `α : F ⟶ L₂ ⋙ RF` is the right derived functor of `F` iff
for any `X₁ : C₁`, the map `α.app (Φ.functor.obj X₁)` is an isomorphism.

-/

public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Limits Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H]
  {D₂ : Type u₄} [Category.{v₄} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂) (F : C₂ ⥤ H)

/-- Given a localizer morphism `Φ : LocalizerMorphism W₁ W₂` between
morphism properties on `C₁` and `C₂`, and a functor `C₂ ⥤ H`, this
is the property that `W₁` is inverted by `Φ.functor ⋙ F`.
In case `Φ` is a (left/right) derivability structure, this allows
the construction of a derived functor for `F` relatively to `W₂`. -/
/-
**CategoryTheory.LocalizerMorphism.Derives** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.LocalizerMorphism`。
形式化陈述：Derives : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a localizer morphism `Φ : LocalizerMorphism W₁ W₂` between
morphism properties on `C₁` and `C₂`, and a functor `C₂ ⥤ H`, this
is the property that `W₁` is inverted by `Φ.functor ⋙ F`.
In case `Φ` is a (left/right) derivability structure, this allows
the construction of a derived functor for `F` relatively to `W₂`.
-/
abbrev Derives : Prop := W₁.IsInvertedBy (Φ.functor ⋙ F)

namespace Derives

variable {Φ F} (h : Φ.Derives F) [Φ.IsRightDerivabilityStructure]

include h

/-
**CategoryTheory.LocalizerMorphism.Derives.hasPointwiseRightDerivedFunctor** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism.Derives`。
形式化陈述：hasPointwiseRightDerivedFunctor : F.HasPointwiseRightDerivedFunctor W₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.hasPointwiseRightDerivedFunctor_iff_of_
isRightDerivabilityStructure`：hasPointwiseRightDerivedFunctor_iff_of_isRightDeri
vabilityStructure : F.HasPointwiseRightDerivedFunctor W₂ ↔ ((Φ.functor ⋙ F).HasP
ointwiseRi…
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightDerivedFunctor_of_inverts`：hasPo
intwiseRightDerivedFunctor_of_inverts (F : C ⥤ H) {W : MorphismProperty C} (hF :
 W.IsInvertedBy F) : F.HasPointwiseRightDerivedFunctor …
-/
lemma hasPointwiseRightDerivedFunctor : F.HasPointwiseRightDerivedFunctor W₂ := by
  rw [hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure Φ F]
  exact Functor.hasPointwiseRightDerivedFunctor_of_inverts _ h

section

variable {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {RF : D₂ ⥤ H} (α : F ⟶ L₂ ⋙ RF)

/-
**CategoryTheory.LocalizerMorphism.Derives.isIso_of_isRightDerivedFunctor** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism.Derives`。
形式化陈述：isIso_of_isRightDerivedFunctor (X₁ : C₁) [RF.IsRightDerivedFunctor α W₂] :
 IsIso (α.app (Φ.functor.obj X₁))
参数：X₁ : C₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isRightDerivedFunctor_of_inverts`：isRightDerivedF
unctor_of_inverts [L.IsLocalization W] (F' : D ⥤ H) (e : L ⋙ F' ≅ F) : F'.IsRigh
tDerivedFunctor e.inv W where isLeftKanExtens…
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightDerivedFunctor_of_inverts`：hasPo
intwiseRightDerivedFunctor_of_inverts (F : C ⥤ H) {W : MorphismProperty C} (hF :
 W.IsInvertedBy F) : F.HasPointwiseRightDerivedFunctor …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.LocalizerMorphism.isIso_iff_of_isRightDerivabilityStructu
re`：isIso_iff_of_isRightDerivabilityStructure (X : C₁) : IsIso (α₁.app X) ↔ IsIs
o (α₂.app (Φ.functor.obj X))
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
-/
lemma isIso_of_isRightDerivedFunctor (X₁ : C₁) [RF.IsRightDerivedFunctor α W₂] :
    IsIso (α.app (Φ.functor.obj X₁)) := by
  let G : W₁.Localization ⥤ H := Localization.lift (Φ.functor ⋙ F) h W₁.Q
  let eG := Localization.Lifting.iso W₁.Q W₁ (Φ.functor ⋙ F) G
  have := Functor.isRightDerivedFunctor_of_inverts W₁ G eG
  have := (Φ.functor ⋙ F).hasPointwiseRightDerivedFunctor_of_inverts h
  rw [← Φ.isIso_iff_of_isRightDerivabilityStructure W₁.Q L₂ F G eG.inv RF α]
  infer_instance

@[deprecated (since := "2026-06-22")] alias isIso := isIso_of_isRightDerivedFunctor

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.LocalizerMorphism.Derives.isRightDerivedFunctor_of_isIso** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism.Derives`。
形式化陈述：isRightDerivedFunctor_of_isIso (hα : forall (X₁ : C₁), IsIso (α.app (Φ.fun
ctor.obj X₁))) : RF.IsRightDerivedFunctor α W₂
参数：hα : forall (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.Derives.hasPointwiseRightDerivedFunctor
`：hasPointwiseRightDerivedFunctor : F.HasPointwiseRightDerivedFunctor W₂
· 使用引理 `CategoryTheory.Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerive
dFunctor`：hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor : F.HasRight
DerivedFunctor W where hasLeftKanExtension'
· 使用引理 `CategoryTheory.LocalizerMorphism.Derives.isIso_of_isRightDerivedFunctor`
：isIso_of_isRightDerivedFunctor (X₁ : C₁) [RF.IsRightDerivedFunctor α W₂] : IsIs
o (α.app (Φ.functor.obj X₁))
· 使用引理 `CategoryTheory.LocalizerMorphism.essSurj_of_hasRightResolutions`：essSurj
_of_hasRightResolutions [Φ.HasRightResolutions] : (Φ.functor ⋙ L₂).EssSurj where
 mem_essImage X₂
· 使用定理 `CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure.hasRightRe
solutions`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, 
u₁} C₁}   {inst_1 : CategoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用定理 `CategoryTheory.Functor.instIsRightDerivedFunctorTotalRightDerivedTotalRi
ghtDerivedUnit`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_3} [inst : CategoryT
heory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_2} …
· 使用引理 `CategoryTheory.Functor.rightDerived_fac`：rightDerived_fac (G : D ⥤ H) (β
 : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (RF.rightDerivedDesc α W G β) = β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.isIso_iff_isIso_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.NatTrans.isIso_app_iff_of_iso`：isIso_app_iff_of_iso {F G 
: C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) : IsIso (α.app X) ↔ IsIso (α.app Y)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.isRightDerivedFunctor_iff_of_iso`：isRightDerivedF
unctor_iff_of_iso (α' : F ⟶ L ⋙ RF') (W : MorphismProperty C) [L.IsLocalization 
W] (e : RF ≅ RF') (comm : α ≫ whiskerLeft L e…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isRightDerivedFunctor_of_isIso (hα : ∀ (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))) :
    RF.IsRightDerivedFunctor α W₂ := by
  have := h.hasPointwiseRightDerivedFunctor
  have := h.isIso_of_isRightDerivedFunctor (F.totalRightDerivedUnit L₂ W₂)
  have := Φ.essSurj_of_hasRightResolutions L₂
  let φ := (F.totalRightDerived L₂ W₂).rightDerivedDesc (F.totalRightDerivedUnit L₂ W₂) W₂ RF α
  have hφ : F.totalRightDerivedUnit L₂ W₂ ≫ Functor.whiskerLeft L₂ φ = α :=
    (F.totalRightDerived L₂ W₂).rightDerived_fac (F.totalRightDerivedUnit L₂ W₂) W₂ RF α
  have : IsIso φ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Y₂
    rw [NatTrans.isIso_app_iff_of_iso φ ((Φ.functor ⋙ L₂).objObjPreimageIso Y₂).symm]
    dsimp
    simp only [← hφ, NatTrans.comp_app, Functor.whiskerLeft_app, isIso_comp_left_iff] at hα
    infer_instance
  rw [← Functor.isRightDerivedFunctor_iff_of_iso (F.totalRightDerivedUnit L₂ W₂) α W₂
    (asIso φ) (by cat_disch)]
  infer_instance
/-
**CategoryTheory.LocalizerMorphism.Derives.isRightDerivedFunctor_iff_isIso** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism.Derives`。
形式化陈述：isRightDerivedFunctor_iff_isIso : RF.IsRightDerivedFunctor α W₂ ↔ forall (
X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.Derives.isIso_of_isRightDerivedFunctor`
：isIso_of_isRightDerivedFunctor (X₁ : C₁) [RF.IsRightDerivedFunctor α W₂] : IsIs
o (α.app (Φ.functor.obj X₁))
· 使用引理 `CategoryTheory.LocalizerMorphism.Derives.isRightDerivedFunctor_of_isIso`
：isRightDerivedFunctor_of_isIso (hα : forall (X₁ : C₁), IsIso (α.app (Φ.functor.
obj X₁))) : RF.IsRightDerivedFunctor α W₂
-/
lemma isRightDerivedFunctor_iff_isIso :
    RF.IsRightDerivedFunctor α W₂ ↔ ∀ (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁)) :=
  ⟨fun _ _ ↦ h.isIso_of_isRightDerivedFunctor α _, h.isRightDerivedFunctor_of_isIso α⟩

end

end Derives

end LocalizerMorphism

end CategoryTheory

