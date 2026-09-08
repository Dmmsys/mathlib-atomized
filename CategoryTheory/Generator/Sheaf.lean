/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Generator.Presheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Generators in the category of sheaves

In this file, we show that if `J : GrothendieckTopology C` and `A` is a preadditive
category which has a separator (and suitable coproducts), then `Sheaf J A` has a separator.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

namespace Sheaf

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C) {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{v} A] [HasWeakSheafify J A]

/-- Given `J : GrothendieckTopology C`, `X : C` and `M : A`, this is the associated
sheaf to the presheaf `Presheaf.freeYoneda X M`. -/
/-
**CategoryTheory.Sheaf.freeYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Shea
f`。
形式化陈述：freeYoneda (X : C) (M : A) : Sheaf J A
参数：X : C；M : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `J : GrothendieckTopology C`, `X : C` and `M : A`, this is the associated
sheaf to the presheaf `Presheaf.freeYoneda X M`.
-/
noncomputable def freeYoneda (X : C) (M : A) : Sheaf J A :=
  (presheafToSheaf J A).obj (Presheaf.freeYoneda X M)

variable {J} in
/-- The bijection `(Sheaf.freeYoneda J X M ⟶ F) ≃ (M ⟶ F.val.obj (op X))`
when `F : Sheaf J A`, `X : C` and `M : A`. -/
/-
**CategoryTheory.Sheaf.freeYonedaHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Sheaf`。
形式化陈述：freeYonedaHomEquiv {X : C} {M : A} {F : Sheaf J A} : (freeYoneda J X M ⟶ F
) ≃ (M ⟶ F.obj.obj (op X))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The bijection `(Sheaf.freeYoneda J X M ⟶ F) ≃ (M ⟶ F.val.obj (op X))`
when `F : Sheaf J A`, `X : C` and `M : A`.
-/
noncomputable def freeYonedaHomEquiv {X : C} {M : A} {F : Sheaf J A} :
    (freeYoneda J X M ⟶ F) ≃ (M ⟶ F.obj.obj (op X)) :=
  ((sheafificationAdjunction J A).homEquiv _ _).trans Presheaf.freeYonedaHomEquiv

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Sheaf.isSeparating** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
eaf`。
形式化陈述：isSeparating {ι : Type w} {S : ι -> A} (hS : ObjectProperty.IsSeparating (
.ofObj S)) : ObjectProperty.IsSeparating (.ofObj (fun (⟨X, i⟩ : C × ι) => freeYo
neda J X (S i)))
参数：hS : ObjectProperty.IsSeparating (.ofObj S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用引理 `CategoryTheory.Presheaf.isSeparating`：isSeparating {ι : Type w} {S : ι -
> A} (hS : ObjectProperty.IsSeparating (.ofObj S)) : ObjectProperty.IsSeparating
 (.ofObj (fun (⟨X, i⟩ : C …
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.ofObj_apply`：ofObj_apply (i : ι) : ofObj X
 (X i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isSeparating {ι : Type w} {S : ι → A} (hS : ObjectProperty.IsSeparating (.ofObj S)) :
    ObjectProperty.IsSeparating (.ofObj (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda J X (S i))) := by
  intro F G f g hfg
  refine (sheafToPresheaf J A).map_injective (Presheaf.isSeparating C hS _ _ ?_)
  rintro _ ⟨X, i⟩ a
  apply ((sheafificationAdjunction _ _).homEquiv _ _).symm.injective
  simpa only [← Adjunction.homEquiv_naturality_right_symm] using
    hfg _ (ObjectProperty.ofObj_apply _ ⟨X, i⟩)
      (((sheafificationAdjunction _ _).homEquiv _ _).symm a)
/-
**CategoryTheory.Sheaf.isSeparator** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.She
af`。
形式化陈述：isSeparator {ι : Type w} {S : ι -> A} (hS : ObjectProperty.IsSeparating (.
ofObj S)) [HasCoproduct (fun (⟨X, i⟩ : C × ι) => freeYoneda J X (S i))] [Preaddi
tive A] : IsSeparator (∐ (fun (⟨X, i⟩ : C × ι) => freeYoneda J X (S i)))
参数：hS : ObjectProperty.IsSeparating (.ofObj S)；fun (⟨X, i⟩ : C × ι) => freeYoned
a J X (S i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.isSeparator_coproduct`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.Limits.Has
ZeroMorphisms C] {β : Type w}   {f : β → C} [inst_2 : …
· 使用引理 `CategoryTheory.Sheaf.isSeparating`：isSeparating {ι : Type w} {S : ι -> A
} (hS : ObjectProperty.IsSeparating (.ofObj S)) : ObjectProperty.IsSeparating (.
ofObj (fun (⟨X, i⟩ : C …
-/
lemma isSeparator {ι : Type w} {S : ι → A} (hS : ObjectProperty.IsSeparating (.ofObj S))
    [HasCoproduct (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda J X (S i))] [Preadditive A] :
    IsSeparator (∐ (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda J X (S i))) :=
  (isSeparating J hS).isSeparator_coproduct

variable (A) in
/-
**CategoryTheory.Sheaf.hasSeparator** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sh
eaf`。
形式化陈述：hasSeparator [HasSeparator A] [Preadditive A] [HasCoproducts.{u} A] : HasS
eparator (Sheaf J A) where hasSeparator
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Sheaf.instHasColimitsOfShape`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} {D : T
ype w}   [inst_1 : CategoryTheory…
· 使用引理 `CategoryTheory.Sheaf.isSeparator`：isSeparator {ι : Type w} {S : ι -> A} 
(hS : ObjectProperty.IsSeparating (.ofObj S)) [HasCoproduct (fun (⟨X, i⟩ : C × ι
) => freeYoneda J X (S…
· 使用定理 `CategoryTheory.isSeparator_separator`：isSeparator_separator [HasSeparato
r C] : IsSeparator (separator C)
-/
instance hasSeparator [HasSeparator A] [Preadditive A] [HasCoproducts.{u} A] :
    HasSeparator (Sheaf J A) where
  hasSeparator := ⟨_, isSeparator J (S := fun (_ : Unit) ↦ separator A)
      (by simpa using! isSeparator_separator A)⟩

end Sheaf

end CategoryTheory

