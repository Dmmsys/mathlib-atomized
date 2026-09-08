/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Stability properties of morphism properties on functor categories

Given `W : MorphismProperty C` and a category `J`, we study the
stability properties of `W.functorCategory J : MorphismProperty (J ⥤ C)`.

Under suitable assumptions, we also show that if monomorphisms
in `C` are stable under transfinite compositions (or coproducts),
then the same holds in the category `J ⥤ C`.

-/

public section

universe v v' v'' u u' u''

namespace CategoryTheory

open Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.IsStableUnderRetracts] (J : Type u'') [Category.{v''} J] :
    (W.functorCategory J).IsStableUnderRetracts where
  of_retract hfg hg j :=
    W.of_retract (hfg.map ((evaluation _ _).obj j)) (hg j)

variable {W}
/-
**CategoryTheory.MorphismProperty.IsStableUnderLimitsOfShape.functorCategory** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderLimitsOfSha
pe`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheo
ry.MorphismProperty C} {K : Type u'}   [inst_1 : CategoryTheory.Category.{v', u'
} K] [W.IsStableUnderLimitsOfShape K] (J : Type u'')   [inst_3 : CategoryTheory.
Category.{v'', u''} J] [CategoryTheory.Limits.HasLimitsOfShape K C],   (W.functo
rCategory J).IsStableUnderLimitsOfShape K
参数：J : Type u''；W.functorCategory J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.limitsOfShape_le`：limitsOfShape_le [W.Is
StableUnderLimitsOfShape J] : W.limitsOfShape J <= W
· 使用定理 `CategoryTheory.MorphismProperty.limitsOfShape.mk'`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W : CategoryTheory.MorphismProperty C} {J :
 Type u_1}   [inst_1 : CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
-/
instance IsStableUnderLimitsOfShape.functorCategory
    {K : Type u'} [Category.{v'} K] [W.IsStableUnderLimitsOfShape K]
    (J : Type u'') [Category.{v''} J] [HasLimitsOfShape K C] :
    (W.functorCategory J).IsStableUnderLimitsOfShape K where
  condition X₁ X₂ _ _ hc₁ hc₂ f hf φ hφ j :=
    MorphismProperty.limitsOfShape_le _
      (limitsOfShape.mk' (X₁ ⋙ (evaluation _ _).obj j) (X₂ ⋙ (evaluation _ _).obj j)
      _ _ (isLimitOfPreserves _ hc₁) (isLimitOfPreserves _ hc₂) (Functor.whiskerRight f _)
      (fun k ↦ hf k j) (φ.app j) (fun k ↦ congr_app (hφ k) j))
/-
**CategoryTheory.MorphismProperty.IsStableUnderColimitsOfShape.functorCategory**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderColimitsO
fShape`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheo
ry.MorphismProperty C} {K : Type u'}   [inst_1 : CategoryTheory.Category.{v', u'
} K] [W.IsStableUnderColimitsOfShape K] (J : Type u'')   [inst_3 : CategoryTheor
y.Category.{v'', u''} J] [CategoryTheory.Limits.HasColimitsOfShape K C],   (W.fu
nctorCategory J).IsStableUnderColimitsOfShape K
参数：J : Type u''；W.functorCategory J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_le`：colimitsOfShape_le [
W.IsStableUnderColimitsOfShape J] : W.colimitsOfShape J <= W
· 使用定理 `CategoryTheory.MorphismProperty.colimitsOfShape.mk'`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.MorphismProperty C} {J
 : Type u_1}   [inst_1 : CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
-/
instance IsStableUnderColimitsOfShape.functorCategory
    {K : Type u'} [Category.{v'} K] [W.IsStableUnderColimitsOfShape K]
    (J : Type u'') [Category.{v''} J] [HasColimitsOfShape K C] :
    (W.functorCategory J).IsStableUnderColimitsOfShape K where
  condition X₁ X₂ _ _ hc₁ hc₂ f hf φ hφ j :=
    MorphismProperty.colimitsOfShape_le _
      (colimitsOfShape.mk' (X₁ ⋙ (evaluation _ _).obj j) (X₂ ⋙ (evaluation _ _).obj j)
      _ _ (isColimitOfPreserves _ hc₁) (isColimitOfPreserves _ hc₂) (Functor.whiskerRight f _)
      (fun k ↦ hf k j) (φ.app j) (fun k ↦ congr_app (hφ k) j))
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.IsStableUnderBaseChange] (J : Type u'') [Category.{v''} J] [HasPullbacks C] :
    (W.functorCategory J).IsStableUnderBaseChange where
  of_isPullback sq hr j :=
    W.of_isPullback (sq.map ((evaluation _ _).obj j)) (hr j)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.IsStableUnderCobaseChange] (J : Type u'') [Category.{v''} J] [HasPushouts C] :
    (W.functorCategory J).IsStableUnderCobaseChange where
  of_isPushout sq hr j :=
    W.of_isPushout (sq.map ((evaluation _ _).obj j)) (hr j)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : Type u') [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K]
    [W.IsStableUnderTransfiniteCompositionOfShape K] (J : Type u'') [Category.{v''} J]
    [HasIterationOfShape K C] :
    (W.functorCategory J).IsStableUnderTransfiniteCompositionOfShape K where
  le := by
    rintro X Y f ⟨hf⟩ j
    have : W.functorCategory J ≤ W.inverseImage ((evaluation _ _).obj j) := fun _ _ _ h ↦ h _
    exact W.transfiniteCompositionsOfShape_le K _ ⟨(hf.ofLE this).map⟩

variable (J : Type u'') [Category.{v''} J]
/-
**CategoryTheory.MorphismProperty.functorCategory_isomorphisms** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：functorCategory_isomorphisms : (isomorphisms C).functorCategory J = isomor
phisms (J ⥤ C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma functorCategory_isomorphisms :
    (isomorphisms C).functorCategory J = isomorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, isomorphisms.iff, NatTrans.isIso_iff_isIso_app]
/-
**CategoryTheory.MorphismProperty.functorCategory_monomorphisms** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：functorCategory_monomorphisms [HasPullbacks C] : (monomorphisms C).functor
Category J = monomorphisms (J ⥤ C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma functorCategory_monomorphisms [HasPullbacks C] :
    (monomorphisms C).functorCategory J = monomorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, monomorphisms.iff, NatTrans.mono_iff_mono_app]
/-
**CategoryTheory.MorphismProperty.functorCategory_epimorphisms** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：functorCategory_epimorphisms [HasPushouts C] : (epimorphisms C).functorCat
egory J = epimorphisms (J ⥤ C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma functorCategory_epimorphisms [HasPushouts C] :
    (epimorphisms C).functorCategory J = epimorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, epimorphisms.iff, NatTrans.epi_iff_epi_app]
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : Type u') [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K]
    [(monomorphisms C).IsStableUnderTransfiniteCompositionOfShape K]
    [HasPullbacks C] [HasIterationOfShape K C] :
    (monomorphisms (J ⥤ C)).IsStableUnderTransfiniteCompositionOfShape K := by
  rw [← functorCategory_monomorphisms]
  infer_instance
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K' : Type u') [(monomorphisms C).IsStableUnderCoproductsOfShape K']
    [HasCoproductsOfShape K' C] [HasPullbacks C] :
    (monomorphisms (J ⥤ C)).IsStableUnderCoproductsOfShape K' := by
  rw [← functorCategory_monomorphisms]
  infer_instance
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsStableUnderCoproducts.{u'} (monomorphisms C)]
    [HasCoproducts.{u'} C] [HasPullbacks C] :
    IsStableUnderCoproducts.{u'} (monomorphisms (J ⥤ C)) where

end MorphismProperty

end CategoryTheory

