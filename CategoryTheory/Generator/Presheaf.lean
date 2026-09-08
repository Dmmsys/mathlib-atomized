/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Generators in the category of presheaves

In this file, we show that if `A` is a category with zero morphisms that
has a separator (and suitable coproducts), then the category of
presheaves `Cᵒᵖ ⥤ A` also has a separator.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

namespace Presheaf

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{v} A]

/-- Given `X : C` and `M : A`, this is the presheaf `Cᵒᵖ ⥤ A` which sends
`Y : Cᵒᵖ` to the coproduct of copies of `M` indexed by `Y.unop ⟶ X`. -/
@[simps]
/-
**CategoryTheory.Presheaf.freeYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.P
resheaf`。
形式化陈述：freeYoneda (X : C) (M : A) : Cᵒᵖ ⥤ A where obj Y
参数：X : C；M : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : C` and `M : A`, this is the presheaf `Cᵒᵖ ⥤ A` which sends
`Y : Cᵒᵖ` to the coproduct of copies of `M` indexed by `Y.unop ⟶ X`.
-/
noncomputable def freeYoneda (X : C) (M : A) : Cᵒᵖ ⥤ A where
  obj Y := ∐ (fun (i : (yoneda.obj X).obj Y) ↦ M)
  map f := Sigma.map' ((yoneda.obj X).map f) (fun _ ↦ 𝟙 M)

set_option backward.isDefEq.respectTransparency false in
/-- The bijection `(Presheaf.freeYoneda X M ⟶ F) ≃ (M ⟶ F.obj (op X))`. -/
/-
**CategoryTheory.Presheaf.freeYonedaHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Presheaf`。
形式化陈述：freeYonedaHomEquiv {X : C} {M : A} {F : Cᵒᵖ ⥤ A} : (freeYoneda X M ⟶ F) ≃ 
(M ⟶ F.obj (op X)) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(Presheaf.freeYoneda X M ⟶ F) ≃ (M ⟶ F.obj (op X))`.
-/
noncomputable def freeYonedaHomEquiv {X : C} {M : A} {F : Cᵒᵖ ⥤ A} :
    (freeYoneda X M ⟶ F) ≃ (M ⟶ F.obj (op X)) where
  toFun f := Sigma.ι (fun (i : (yoneda.obj X).obj _) ↦ M) (𝟙 _) ≫ f.app (op X)
  invFun g :=
    { app Y := Sigma.desc (fun φ ↦ g ≫ F.map φ.op)
      naturality _ _ _ := Sigma.hom_ext _ _ (by simp) }
  left_inv f := by
    ext Y
    refine Sigma.hom_ext _ _ (fun φ ↦ ?_)
    simpa using (Sigma.ι _ (𝟙 _) ≫= f.naturality φ.op).symm
  right_inv g := by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Presheaf.freeYonedaHomEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Presheaf`。
形式化陈述：freeYonedaHomEquiv_comp {X : C} {M : A} {F G : Cᵒᵖ ⥤ A} (α : freeYoneda X 
M ⟶ F) (f : F ⟶ G) : freeYonedaHomEquiv (α ≫ f) = freeYonedaHomEquiv α ≫ f.app (
op X)
参数：α : freeYoneda X M ⟶ F；f : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma freeYonedaHomEquiv_comp {X : C} {M : A} {F G : Cᵒᵖ ⥤ A}
    (α : freeYoneda X M ⟶ F) (f : F ⟶ G) :
    freeYonedaHomEquiv (α ≫ f) = freeYonedaHomEquiv α ≫ f.app (op X) := by
  simp [freeYonedaHomEquiv]

@[reassoc]
/-
**CategoryTheory.Presheaf.freeYonedaHomEquiv_symm_comp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Presheaf`。
形式化陈述：freeYonedaHomEquiv_symm_comp {X : C} {M : A} {F G : Cᵒᵖ ⥤ A} (α : M ⟶ F.ob
j (op X)) (f : F ⟶ G) : freeYonedaHomEquiv.symm α ≫ f = freeYonedaHomEquiv.symm 
(α ≫ f.app (op X))
参数：α : M ⟶ F.obj (op X)；f : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presheaf.freeYonedaHomEquiv_comp`：freeYonedaHomEquiv_comp
 {X : C} {M : A} {F G : Cᵒᵖ ⥤ A} (α : freeYoneda X M ⟶ F) (f : F ⟶ G) : freeYone
daHomEquiv (α ≫ f) = freeYonedaHomEqu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma freeYonedaHomEquiv_symm_comp {X : C} {M : A} {F G : Cᵒᵖ ⥤ A} (α : M ⟶ F.obj (op X))
    (f : F ⟶ G) :
    freeYonedaHomEquiv.symm α ≫ f = freeYonedaHomEquiv.symm (α ≫ f.app (op X)) := by
  apply freeYonedaHomEquiv.injective
  simp only [freeYonedaHomEquiv_comp, Equiv.apply_symm_apply]

variable (C)
/-
**CategoryTheory.Presheaf.isSeparating** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Presheaf`。
形式化陈述：isSeparating {ι : Type w} {S : ι -> A} (hS : ObjectProperty.IsSeparating (
.ofObj S)) : ObjectProperty.IsSeparating (.ofObj (fun (⟨X, i⟩ : C × ι) => freeYo
neda X (S i)))
参数：hS : ObjectProperty.IsSeparating (.ofObj S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presheaf.freeYonedaHomEquiv_symm_comp`：freeYonedaHomEquiv
_symm_comp {X : C} {M : A} {F G : Cᵒᵖ ⥤ A} (α : M ⟶ F.obj (op X)) (f : F ⟶ G) : 
freeYonedaHomEquiv.symm α ≫ f = freeYoneda…
· 使用引理 `CategoryTheory.ObjectProperty.ofObj_apply`：ofObj_apply (i : ι) : ofObj X
 (X i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isSeparating {ι : Type w} {S : ι → A} (hS : ObjectProperty.IsSeparating (.ofObj S)) :
    ObjectProperty.IsSeparating (.ofObj (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda X (S i))) := by
  intro F G f g h
  ext ⟨X⟩
  refine hS _ _ ?_
  rintro _ ⟨i⟩ α
  apply freeYonedaHomEquiv.symm.injective
  simpa only [freeYonedaHomEquiv_symm_comp] using
    h _ (ObjectProperty.ofObj_apply _ ⟨X, i⟩) (freeYonedaHomEquiv.symm α)
/-
**CategoryTheory.Presheaf.isSeparator** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Presheaf`。
形式化陈述：isSeparator {ι : Type w} {S : ι -> A} (hS : ObjectProperty.IsSeparating (.
ofObj S)) [HasCoproduct (fun (⟨X, i⟩ : C × ι) => freeYoneda X (S i))] [HasZeroMo
rphisms A] : IsSeparator (∐ (fun (⟨X, i⟩ : C × ι) => freeYoneda X (S i)))
参数：hS : ObjectProperty.IsSeparating (.ofObj S)；fun (⟨X, i⟩ : C × ι) => freeYoned
a X (S i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.isSeparator_coproduct`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.Limits.Has
ZeroMorphisms C] {β : Type w}   {f : β → C} [inst_2 : …
· 使用引理 `CategoryTheory.Presheaf.isSeparating`：isSeparating {ι : Type w} {S : ι -
> A} (hS : ObjectProperty.IsSeparating (.ofObj S)) : ObjectProperty.IsSeparating
 (.ofObj (fun (⟨X, i⟩ : C …
-/
lemma isSeparator {ι : Type w} {S : ι → A} (hS : ObjectProperty.IsSeparating (.ofObj S))
    [HasCoproduct (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda X (S i))]
    [HasZeroMorphisms A] :
    IsSeparator (∐ (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda X (S i))) :=
  (isSeparating C hS).isSeparator_coproduct

variable (A) in
/-
**CategoryTheory.Presheaf.hasSeparator** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Presheaf`。
形式化陈述：hasSeparator [HasSeparator A] [HasZeroMorphisms A] [HasCoproducts.{u} A] :
 HasSeparator (Cᵒᵖ ⥤ A) where hasSeparator
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.Presheaf.isSeparator`：isSeparator {ι : Type w} {S : ι -> 
A} (hS : ObjectProperty.IsSeparating (.ofObj S)) [HasCoproduct (fun (⟨X, i⟩ : C 
× ι) => freeYoneda X (S i…
· 使用定理 `CategoryTheory.isSeparator_separator`：isSeparator_separator [HasSeparato
r C] : IsSeparator (separator C)
-/
instance hasSeparator [HasSeparator A] [HasZeroMorphisms A] [HasCoproducts.{u} A] :
    HasSeparator (Cᵒᵖ ⥤ A) where
  hasSeparator := ⟨_, isSeparator C (S := fun (_ : Unit) ↦ separator A)
      (by simpa using! isSeparator_separator A)⟩

end Presheaf

end CategoryTheory

