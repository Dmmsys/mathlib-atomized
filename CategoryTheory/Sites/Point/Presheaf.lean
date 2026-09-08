/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Points of presheaf toposes

Let `C` be a category. For the Grothendieck topology `⊥` on `C`, we know
that the category of sheaves with values in `A` identifies to `Cᵒᵖ ⥤ A`
(see `sheafBotEquivalence` in the file `Mathlib/CategoryTheory/Sites/Sheaf.lean`).
In this file, we show that any `X : C` defines a point for this site, and that
these points form a conservative family of points.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]

namespace GrothendieckTopology

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `X` is an object of `C`, this is the point of the site `(C, ⊥)` (whose
sheaves are presheaves, see `sheafBotEquivalence`) corresponding to `X`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.pointBot** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.GrothendieckTopology`。
形式化陈述：pointBot (X : C) : Point.{w} (⊥ : GrothendieckTopology C) where fiber
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is an object of `C`, this is the point of the site `(C, ⊥)` (whose
sheaves are presheaves, see `sheafBotEquivalence`) corresponding to `X`.
-/
noncomputable def pointBot (X : C) :
    Point.{w} (⊥ : GrothendieckTopology C) where
  fiber := shrinkYoneda.flip.obj (op X)
  jointly_surjective {U} R hR x := by
    obtain rfl : R = ⊤ := by simpa using hR
    exact ⟨U, 𝟙 _, by simp, x, by simp⟩

/-- The functor `C ⥤ Point.{w} (⊥ : GrothendieckTopology C)` which sends
`X : C` to the point corresponding to `X`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.pointBotFunctor** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.GrothendieckTopology`。
形式化陈述：pointBotFunctor : C ⥤ Point.{w} (⊥ : GrothendieckTopology C) where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `C ⥤ Point.{w} (⊥ : GrothendieckTopology C)` which sends
`X : C` to the point corresponding to `X`.
-/
noncomputable def pointBotFunctor :
    C ⥤ Point.{w} (⊥ : GrothendieckTopology C) where
  obj := pointBot
  map f := { hom := shrinkYoneda.flip.map f.op }

section

variable (X : C) (A : Type*) [Category A] [HasColimitsOfSize.{w, w} A]

/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance :
    IsIso ((pointBot.{w} X).toPresheafFiberNatTrans (A := A) X
      (shrinkYonedaObjObjEquiv.symm (𝟙 X))) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun _ ↦ (colimit.isColimit _).isIso_ι_app_of_isTerminal _
    (Functor.Elements.isInitialElementsMkShrinkYonedaObjObjEquivId X).op

/-- The fiber functor `(Cᵒᵖ ⥤ A) ⥤ A` corresponding to the point
of the Grothendieck topology `⊥` attached to an object `X : C`
identifies to the evaluation functor at `X`. -/
@[simps! inv]
/-
**CategoryTheory.GrothendieckTopology.pointBotPresheafFiberIso** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：pointBotPresheafFiberIso : (pointBot.{w} X).presheafFiber (A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsIsoFunctorOppositeToPresheafFi
berNatTransPointBotCoeEquivHomUnopOpObjTypeShrinkYonedaSymmShrinkYonedaObjObjEqu
ivId`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.LocallySmall.{w, v, u} C] (X : C)   (A : Type u_1) [inst_2…

--- 原说明 ---
The fiber functor `(Cᵒᵖ ⥤ A) ⥤ A` corresponding to the point
of the Grothendieck topology `⊥` attached to an object `X : C`
identifies to the evaluation functor at `X`.
-/
noncomputable def pointBotPresheafFiberIso :
    (pointBot.{w} X).presheafFiber (A := A) ≅
      (evaluation Cᵒᵖ A).obj (op X) :=
  (asIso ((pointBot X).toPresheafFiberNatTrans X
      (shrinkYonedaObjObjEquiv.symm (𝟙 X)))).symm

end

variable (C) in
/-- The family of points on the site `(C, ⊥)` (whose
sheaves are presheaves, see `sheafBotEquivalence`) given by the objects of `X`. -/
/-
**CategoryTheory.GrothendieckTopology.pointsBot** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.GrothendieckTopology`。
形式化陈述：pointsBot : ObjectProperty (Point.{w} (⊥ : GrothendieckTopology C))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of points on the site `(C, ⊥)` (whose
sheaves are presheaves, see `sheafBotEquivalence`) given by the objects of `X`.
-/
noncomputable def pointsBot :
    ObjectProperty (Point.{w} (⊥ : GrothendieckTopology C)) :=
  .ofObj pointBot
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{w} C] : ObjectProperty.Small.{w} (pointsBot C) := by
  dsimp [pointsBot]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (C) in
/-
**CategoryTheory.GrothendieckTopology.isConservative_pointsBot** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：isConservative_pointsBot : (pointsBot.{w} C).IsConservativeFamilyOfPoints
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.mk'`：mk' [Has
Sheafify J (Type w)] (hP : forall ⦃X : C⦄ (S : Sieve X) (_ : forall (Φ : P.FullS
ubcategory) (x : Φ.obj.fiber.obj X), exists (Y : C) …
· 使用定理 `CategoryTheory.instHasSheafifyBotGrothendieckTopology`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] (A : Type u₂) [inst_1 : CategoryTheor
y.Category.{v₂, u₂} A],   CategoryTheory.Ha…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm`：shrink
Yoneda_map_app_shrinkYonedaObjObjEquiv_symm {X X' : C} {Y : Cᵒᵖ} (f : Y.unop ⟶ X
) (g : X ⟶ X') : (shrinkYoneda.map g).app _ (shrinkYon…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
-/
lemma isConservative_pointsBot :
    (pointsBot.{w} C).IsConservativeFamilyOfPoints :=
  .mk' (fun X S hS ↦ by
    obtain ⟨Y, a, ha, b, hb⟩ := hS ⟨_, ⟨X⟩⟩ (shrinkYonedaObjObjEquiv.symm (𝟙 X))
    obtain ⟨b, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective b
    dsimp at b hb
    have : b ≫ a = 𝟙 _ :=
      shrinkYonedaObjObjEquiv.symm.injective (by
        rw [← hb, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm])
    simpa only [bot_covering, ← Sieve.id_mem_iff_eq_top, this]
      using S.downward_closed ha b)
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type w} [SmallCategory C] :
    HasEnoughPoints.{w} (⊥ : GrothendieckTopology C) :=
  ⟨_, inferInstance, isConservative_pointsBot C⟩

end GrothendieckTopology

end CategoryTheory

