/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Sites.Point.Monoidal

/-!
# Monoidal structure on sheaves using enough points

Let `(C, J)` be a site with a conservative family of points.
If `A` is a suitable monoidal category, we show that
the class of morphisms `J.W : MorphismProperty (Cᵒᵖ ⥤ A)`
is stable under tensor products, which allows to
check the assumptions of `Sheaf.monoidalCategory` in the
file `Mathlib/CategoryTheory/Sites/Monoidal.lean`,
i.e. this can be used in order to construct the monoidal
category structure on `Sheaf J A`.

-/

public section

universe w v v' u u'

namespace CategoryTheory

open Limits GrothendieckTopology MonoidalCategory

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}
  {P : ObjectProperty (Point.{w} J)} (hP : P.IsConservativeFamilyOfPoints)
  (A : Type u') [Category.{v'} A] [MonoidalCategory A]
  [HasColimitsOfSize.{w, w} A] [HasProducts.{w} A]
  {FC : A → A → Type*} {CC : A → Type w}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w} A FC]
  [HasWeakSheafify J A]
  [(forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]

include hP in
/-
**CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.isMonoidal_W** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints`
。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
ocallySmall.{w, v, u} C]   {J : CategoryTheory.GrothendieckTopology C} {P : Cate
goryTheory.ObjectProperty J.Point},   P.IsConservativeFamilyOfPoints →     ∀ (A 
: Type u') [inst_2 : CategoryTheory.Category.{v', u'} A] [inst_3 : CategoryTheor
y.MonoidalCategory A]       [CategoryTheory.Limits.HasColimitsOfSize.{w, w, v', 
u'} A] [CategoryTheory.Limits.HasProducts A]       {FC : A → A → Type u_1} {CC :
 A → Type w} [inst_6 : (X Y : A) → FunLike (FC X Y) (CC X) (CC Y)]       [inst_7
 : CategoryTheory.ConcreteCategory A FC] [CategoryTheory.HasWeakSheafify J A]   
    [(CategoryTheory.forget A).ReflectsIsomorphisms]       [CategoryTheory.Limit
s.PreservesFilteredColimitsOfSize.{w, w, v', w, u', w + 1} (CategoryTheory.forge
t A)]       [∀ (X : A),           CategoryTheory.Limits.PreservesFilteredColimit
sOfSize.{w, w, v', v', u', u'}             (CategoryTheory.MonoidalCategory.tens
orLeft X)]       [∀ (X : A),           CategoryTheory.Limits.PreservesFilteredCo
limitsOfSize.{w, w, v', v', u', u'}             (CategoryTheory.MonoidalCategory
.tensorRight X)]       [J.HasSheafCompose (CategoryTheory.forget A)], J.W.IsMono
idal
参数：A : Type u'；X Y : A；FC X Y；CC X；CC Y；CategoryTheory.forget A；CategoryTheory.f
orget A；X : A；CategoryTheory.MonoidalCategory.tensorLeft X；X : A；CategoryTheory.
MonoidalCategory.tensorRight X；CategoryTheory.forget A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMonoidal.mk'`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] (W : CategoryTheory.MorphismProperty C)  
 [inst_1 : CategoryTheory.MonoidalCa…
· 使用定理 `CategoryTheory.ObjectProperty.instIsMultiplicativeIsLocal`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.ObjectProp
erty C),   P.isLocal.IsMultiplicative
· 使用引理 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.W_iff`：W_iff 
{F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [HasWeakSheafify J A] [HasProducts.{w} A] : J.W f ↔ 
forall (Φ : P.FullSubcategory), IsIso (Φ.obj.presheafF…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.Monoidal.map_tensor`：map_tensor {X Y X' Y' : C} (
f : X ⟶ Y) (g : X' ⟶ Y') : F.map (f otimesₘ g) = δ F X X' ≫ (F.map f otimesₘ F.m
ap g) ≫ μ F Y Y'
· 使用定理 `CategoryTheory.Functor.Monoidal.instIsIsoδ`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D 
: Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.instIsIsoμ`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D 
: Type u₂}   [inst_2 : CategoryT…
-/
lemma ObjectProperty.IsConservativeFamilyOfPoints.isMonoidal_W
    [J.HasSheafCompose (forget A)] :
    (J.W (A := A)).IsMonoidal :=
  .mk' _ (fun f g hf hg ↦ by
    simp only [hP.W_iff (A := A)] at hf hg ⊢
    intro Φ
    rw [Functor.Monoidal.map_tensor]
    infer_instance)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [J.HasSheafCompose (forget A)] [HasEnoughPoints.{w} J] :
    (J.W (A := A)).IsMonoidal := by
  obtain ⟨P, _, hP⟩ := HasEnoughPoints.exists_objectProperty J
  exact hP.isMonoidal_W A

end CategoryTheory

