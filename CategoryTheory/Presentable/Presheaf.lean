/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Generator.Presheaf
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Presentable.StrongGenerator

/-!
# Categories of presheaves are locally presentable

If `A` is a locally `κ`-presentable category and `C` is a small category,
we show that `Cᵒᵖ ⥤ A` is also locally `κ`-presentable, under the
additional assumption that `A` has pullbacks (a condition which should
be automatically satisfied (TODO)).

-/

public section

universe w v v' u u'

namespace CategoryTheory

open Opposite Limits

namespace Presheaf

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] freeYonedaHomEquiv_comp in
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
    [HasColimitsOfSize.{w, w} A] [HasCoproducts.{v} A]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] (X : C) (M : A)
    [IsCardinalPresentable M κ] :
    IsCardinalPresentable (freeYoneda X M) κ := by
  let e : coyoneda.obj (op (freeYoneda X M)) ≅
      (evaluation Cᵒᵖ A).obj (op X) ⋙ coyoneda.obj (op M) ⋙ uliftFunctor.{u} :=
    NatIso.ofComponents (fun P ↦ Equiv.toIso (freeYonedaHomEquiv.trans Equiv.ulift.symm))
  constructor
  intro J _ _
  have := preservesColimitsOfShape_of_isCardinalPresentable M κ J
  exact preservesColimitsOfShape_of_natIso e.symm

-- TODO: add variants of this result for `yoneda` and `shrinkYoneda`
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type u} [SmallCategory C]
    [HasColimitsOfSize.{w, w} (Type (max u u'))]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] (X : C) :
    IsCardinalPresentable (uliftYoneda.{u'}.obj X) κ where
  preservesColimitOfShape J _ _ := by
    let e : (coyoneda.obj (op (uliftYoneda.{u'}.obj X))) ≅
        (evaluation _ _).obj (op X) ⋙ uliftFunctor :=
      NatIso.ofComponents (fun P ↦ Equiv.toIso (uliftYonedaEquiv.trans Equiv.ulift.symm))
    exact preservesColimitsOfShape_of_natIso e.symm
/-
**CategoryTheory.Presheaf.isStrongGenerator** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Presheaf`。
形式化陈述：isStrongGenerator {A : Type u'} [Category.{v'} A] {P : ObjectProperty A} (
hP : P.IsStrongGenerator) [HasCoproducts.{w} A] [HasPullbacks A] (C : Type w) [S
mallCategory C] : (ObjectProperty.ofObj (fun (T : C × (Subtype P)) => freeYoneda
 T.1 T.2.1)).IsStrongGenerator
参数：hP : P.IsStrongGenerator；C : Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isStrongGenerator_iff`：isStrongGenerator_i
ff : P.IsStrongGenerator ↔ P.IsSeparating ∧ forall ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i
], (forall (G : C) (_ : P G), Function.Su…
· 使用引理 `CategoryTheory.Presheaf.isSeparating`：isSeparating {ι : Type w} {S : ι -
> A} (hS : ObjectProperty.IsSeparating (.ofObj S)) : ObjectProperty.IsSeparating
 (.ofObj (fun (⟨X, i⟩ : C …
· 使用引理 `CategoryTheory.ObjectProperty.ofObj_subtypeVal`：ofObj_subtypeVal (P : Ob
jectProperty C) : ofObj (Subtype.val : Subtype P -> C) = P
· 使用定理 `CategoryTheory.NatTrans.isIso_iff_isIso_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.instMonoAppOfFunctor`：∀ {K : Type u} [inst : CategoryTheo
ry.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C
]   {F G : CategoryTheory…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用引理 `CategoryTheory.ObjectProperty.ofObj_apply`：ofObj_apply (i : ι) : ofObj X
 (X i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Presheaf.freeYonedaHomEquiv_comp`：freeYonedaHomEquiv_comp
 {X : C} {M : A} {F G : Cᵒᵖ ⥤ A} (α : freeYoneda X M ⟶ F) (f : F ⟶ G) : freeYone
daHomEquiv (α ≫ f) = freeYonedaHomEqu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isStrongGenerator
    {A : Type u'} [Category.{v'} A] {P : ObjectProperty A} (hP : P.IsStrongGenerator)
    [HasCoproducts.{w} A] [HasPullbacks A] (C : Type w) [SmallCategory C] :
    (ObjectProperty.ofObj (fun (T : C × (Subtype P)) ↦
      freeYoneda T.1 T.2.1)).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff] at hP ⊢
  obtain ⟨hP₁, hP₂⟩ := hP
  refine ⟨Presheaf.isSeparating (C := C) (ι := Subtype P) (S := Subtype.val)
    (by simpa using hP₁),
    fun P₁ P₂ i _ hi ↦ ?_⟩
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨X⟩
  refine hP₂ _ (fun G hG f ↦ ?_)
  obtain ⟨y, rfl⟩ := freeYonedaHomEquiv.surjective f
  obtain ⟨x, rfl⟩ := hi (freeYoneda X G)
    (ObjectProperty.ofObj_apply (fun (T : C × (Subtype P)) ↦
      freeYoneda T.1 T.2.1) ⟨X, G, hG⟩) y
  exact ⟨freeYonedaHomEquiv x, by simp [freeYonedaHomEquiv_comp]⟩
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type u'} [Category.{v'} A] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable A κ] [HasPullbacks A]
    (C : Type w) [SmallCategory C] :
    IsCardinalLocallyPresentable (Cᵒᵖ ⥤ A) κ := by
  have hA := (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator A κ).1 inferInstance
  obtain ⟨P, _, hP₁, hP₂⟩ := hA
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  refine ⟨_, inferInstance, isStrongGenerator hP₁ C, ?_⟩
  rintro _ ⟨X, G, hG⟩
  have := hP₂ _ hG
  rw [isCardinalPresentable_iff] at this ⊢
  infer_instance
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type u'} [Category.{v'} A] [IsLocallyPresentable.{w} A] [HasPullbacks A]
    (C : Type w) [SmallCategory C] :
    IsLocallyPresentable.{w} (Cᵒᵖ ⥤ A) where
  exists_cardinal := by
    obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} A
    exact ⟨κ, inferInstance, inferInstance⟩

end Presheaf

end CategoryTheory

