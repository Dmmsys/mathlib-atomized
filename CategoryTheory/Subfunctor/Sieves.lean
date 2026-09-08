/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# Sieves attached to subpresheaves

Given a subpresheaf `G` of a presheaf of types `F : Cᵒᵖ ⥤ Type w` and
a section `s : F.obj U`, we define a sieve `G.sieveOfSection s : Sieve (unop U)`
and the associated compatible family of elements with values in `G.toFunctor`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory.Subfunctor

open Opposite

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w} (G : Subfunctor F)

/-- Given a subpresheaf `G` of `F`, an `F`-section `s` on `U`, we may define a sieve of `U`
consisting of all `f : V ⟶ U` such that the restriction of `s` along `f` is in `G`. -/
@[simps]
/-
**CategoryTheory.Subfunctor.sieveOfSection** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Subfunctor`。
形式化陈述：sieveOfSection {U : Cᵒᵖ} (s : F.obj U) : Sieve (unop U) where arrows V f
参数：s : F.obj U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subpresheaf `G` of `F`, an `F`-section `s` on `U`, we may define a sieve
 of `U`
consisting of all `f : V ⟶ U` such that the restriction of `s` along `f` is in `
G`.
-/
def sieveOfSection {U : Cᵒᵖ} (s : F.obj U) : Sieve (unop U) where
  arrows V f := F.map f.op s ∈ G.obj (op V)
  downward_closed := @fun V W i hi j => by
    simpa using G.map _ hi

/-- Given an `F`-section `s` on `U` and a subpresheaf `G`, we may define a family of elements in
`G` consisting of the restrictions of `s` -/
/-
**CategoryTheory.Subfunctor.familyOfElementsOfSection** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Subfunctor`。
形式化陈述：familyOfElementsOfSection {U : Cᵒᵖ} (s : F.obj U) : (G.sieveOfSection s).1
.FamilyOfElements G.toFunctor
参数：s : F.obj U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `F`-section `s` on `U` and a subpresheaf `G`, we may define a family of
 elements in
`G` consisting of the restrictions of `s`
-/
def familyOfElementsOfSection {U : Cᵒᵖ} (s : F.obj U) :
    (G.sieveOfSection s).1.FamilyOfElements G.toFunctor := fun _ i hi => ⟨F.map i.op s, hi⟩
/-
**CategoryTheory.Subfunctor.family_of_elements_compatible** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Subfunctor`。
形式化陈述：family_of_elements_compatible {U : Cᵒᵖ} (s : F.obj U) : (G.familyOfElement
sOfSection s).Compatible
参数：s : F.obj U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
-/
theorem family_of_elements_compatible {U : Cᵒᵖ} (s : F.obj U) :
    (G.familyOfElementsOfSection s).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  refine Subtype.ext ?_ -- Porting note: `ext1` does not work here
  change F.map g₁.op (F.map f₁.op s) = F.map g₂.op (F.map f₂.op s)
  rw [← comp_apply, ← Functor.map_comp, ← comp_apply, ← Functor.map_comp, ← op_comp, ← op_comp, e]

end CategoryTheory.Subfunctor

