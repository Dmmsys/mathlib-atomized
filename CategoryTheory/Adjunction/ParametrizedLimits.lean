/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Parametrized adjunctions and limits

Given bifunctors `F : C₁ ⥤ C₂ ⥤ C₃`, `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂` and
a parametrized adjunction `adj₂ : F ⊣₂ G`, we show that for any `X₃ : C₃`,
the functor `G.flip.obj X₃ : C₁ᵒᵖ ⥤ C₃` preserves limits of shape `J`
if for any `X₂ : C₂`, the functor `F.flip.obj X₂ : C₁ ⥤ C₃`
preserves colimits of shape `Jᵒᵖ`.

-/

@[expose] public section

namespace CategoryTheory.ParametrizedAdjunction

open Limits Opposite

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂}
  (adj₂ : F ⊣₂ G) {J : Type*} [Category* J]

include adj₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ParametrizedAdjunction.preservesLimit_flip_obj** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：preservesLimit_flip_obj (P : J ⥤ C₁ᵒᵖ) [forall (X₂ : C₂), PreservesColimit
 P.leftOp (F.flip.obj X₂)] (X₃ : C₃) : PreservesLimit P (G.flip.obj X₃) where pr
eserves {c} hc
参数：P : J ⥤ C₁ᵒᵖ；X₂ : C₂；F.flip.obj X₂；X₃ : C₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用引理 `CategoryTheory.ParametrizedAdjunction.homEquiv_symm_naturality_one`：homE
quiv_symm_naturality_one (f₁ : X₁ ⟶ Y₁) (g : X₂ ⟶ (G.obj (op Y₁)).obj X₃) : adj₂
.homEquiv.symm (g ≫ (G.map f₁.op).app X₃) = (F.map f₁).a…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ParametrizedAdjunction.homEquiv_naturality_one`：homEquiv_
naturality_one (f₁ : X₁ ⟶ Y₁) (g : (F.obj Y₁).obj X₂ ⟶ X₃) : adj₂.homEquiv ((F.m
ap f₁).app X₂ ≫ g) = adj₂.homEquiv g ≫ (G.map f₁.op…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `CategoryTheory.Limits.IsColimit.uniq`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u
₃} C]   {F : CategoryTheor…
-/
lemma preservesLimit_flip_obj (P : J ⥤ C₁ᵒᵖ)
    [∀ (X₂ : C₂), PreservesColimit P.leftOp (F.flip.obj X₂)] (X₃ : C₃) :
    PreservesLimit P (G.flip.obj X₃) where
  preserves {c} hc := ⟨by
    let cocone (s : Cone (P ⋙ G.flip.obj X₃)) :
        Cocone (P.leftOp ⋙ F.flip.obj s.pt) :=
      { pt := X₃
        ι.app j := adj₂.homEquiv.symm (s.π.app j.unop)
        ι.naturality _ _ f := by
          simp [← s.w f.unop, dsimp% adj₂.homEquiv_symm_naturality_one (P.map f.unop).unop] }
    let hc' (s : Cone (P ⋙ G.flip.obj X₃)) :=
      isColimitOfPreserves (F.flip.obj s.pt) (isColimitCoconeLeftOpOfCone _ hc)
    exact {
      lift s := adj₂.homEquiv ((hc' s).desc (cocone s))
      fac s j := by
        dsimp
        rw [← dsimp% adj₂.homEquiv_naturality_one (c.π.app j).unop,
          dsimp% (hc' s).fac (cocone s) (op j)]
        simp [cocone]
      uniq s m hm := adj₂.homEquiv.symm.injective (by
        simp only [op_unop, Equiv.symm_apply_apply]
        refine (hc' s).uniq (cocone s) _ (fun j ↦ ?_)
        simp [cocone, ← hm,
          dsimp% adj₂.homEquiv_symm_naturality_one (c.π.app j.unop).unop]) }⟩

variable (J) in
/-
**CategoryTheory.ParametrizedAdjunction.preservesLimitsOfShape_flip_obj** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：preservesLimitsOfShape_flip_obj [forall (X₂ : C₂), PreservesColimitsOfShap
e Jᵒᵖ (F.flip.obj X₂)] (X₃ : C₃) : PreservesLimitsOfShape J (G.flip.obj X₃) wher
e preservesLimit
参数：X₂ : C₂；F.flip.obj X₂；X₃ : C₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ParametrizedAdjunction.preservesLimit_flip_obj`：preserves
Limit_flip_obj (P : J ⥤ C₁ᵒᵖ) [forall (X₂ : C₂), PreservesColimit P.leftOp (F.fl
ip.obj X₂)] (X₃ : C₃) : PreservesLimit P (G.flip.ob…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
lemma preservesLimitsOfShape_flip_obj
    [∀ (X₂ : C₂), PreservesColimitsOfShape Jᵒᵖ (F.flip.obj X₂)] (X₃ : C₃) :
    PreservesLimitsOfShape J (G.flip.obj X₃) where
  preservesLimit := preservesLimit_flip_obj adj₂ _ _

end CategoryTheory.ParametrizedAdjunction

