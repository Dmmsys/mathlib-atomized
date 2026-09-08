/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Constructors for combining (co)fans

We provide constructors for combining (co)fans and show their (co)limit properties.

## TODO

* Combine (co)fans on sigma types

-/

@[expose] public section

universe u₁ u₂

namespace CategoryTheory

namespace Limits

variable {C : Type u₁} [Category.{u₂} C]

namespace Fan

variable {ι₁ ι₂ : Type*} {X : C} {f₁ : ι₁ → C} {f₂ : ι₂ → C}
    (c₁ : Fan f₁) (c₂ : Fan f₂) (bc : BinaryFan c₁.pt c₂.pt)
    (h₁ : IsLimit c₁) (h₂ : IsLimit c₂) (h : IsLimit bc)

/-- For fans on maps `f₁ : ι₁ → C`, `f₂ : ι₂ → C` and a binary fan on their
cone points, construct one family of morphisms indexed by `ι₁ ⊕ ι₂` -/
@[simp]
/-
**CategoryTheory.Limits.Fan.combPairHoms** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.Fan`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{u₂, u₁} C] →     {ι₁ : 
Type u_1} →       {ι₂ : Type u_2} →         {f₁ : ι₁ → C} →           {f₂ : ι₂ →
 C} →             (c₁ : CategoryTheory.Limits.Fan f₁) →               (c₂ : Cate
goryTheory.Limits.Fan f₂) →                 (bc : CategoryTheory.Limits.BinaryFa
n c₁.pt c₂.pt) → (i : ι₁ ⊕ ι₂) → bc.pt ⟶ Sum.elim f₁ f₂ i
参数：c₁ : CategoryTheory.Limits.Fan f₁；c₂ : CategoryTheory.Limits.Fan f₂；bc : Cate
goryTheory.Limits.BinaryFan c₁.pt c₂.pt；i : ι₁ ⊕ ι₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For fans on maps `f₁ : ι₁ → C`, `f₂ : ι₂ → C` and a binary fan on their
cone points, construct one family of morphisms indexed by `ι₁ ⊕ ι₂`
-/
abbrev combPairHoms : (i : ι₁ ⊕ ι₂) → bc.pt ⟶ Sum.elim f₁ f₂ i
  | .inl a => bc.fst ≫ c₁.proj a
  | .inr a => bc.snd ≫ c₂.proj a

variable {c₁ c₂ bc}

set_option backward.isDefEq.respectTransparency false in
/-- If `c₁` and `c₂` are limit fans and `bc` is a limit binary fan on their cone
points, then the fan constructed from `combPairHoms` is a limit cone. -/
/-
**CategoryTheory.Limits.Fan.combPairIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.Fan`。
形式化陈述：combPairIsLimit : IsLimit (Fan.mk bc.pt (combPairHoms c₁ c₂ bc))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `c₁` and `c₂` are limit fans and `bc` is a limit binary fan on their cone
points, then the fan constructed from `combPairHoms` is a limit cone.
-/
def combPairIsLimit : IsLimit (Fan.mk bc.pt (combPairHoms c₁ c₂ bc)) :=
  Fan.IsLimit.mk _
    (fun s ↦ Fan.IsLimit.lift h <| fun i ↦ by
      cases i
      · exact Fan.IsLimit.lift h₁ (fun a ↦ s.proj (.inl a))
      · exact Fan.IsLimit.lift h₂ (fun a ↦ s.proj (.inr a)))
    (fun s w ↦ by
      cases w <;>
      · simp only [fan_mk_proj, combPairHoms]
        erw [← Category.assoc, h.fac]
        simp only [pair_obj_left, mk_π_app, IsLimit.fac])
    (fun s m hm ↦ Fan.IsLimit.hom_ext h _ _ <| fun w ↦ by
      cases w
      · refine Fan.IsLimit.hom_ext h₁ _ _ (fun a ↦ by aesop)
      · refine Fan.IsLimit.hom_ext h₂ _ _ (fun a ↦ by aesop))

end Fan

namespace Cofan

variable {ι₁ ι₂ : Type*} {X : C} {f₁ : ι₁ → C} {f₂ : ι₂ → C}
    (c₁ : Cofan f₁) (c₂ : Cofan f₂) (bc : BinaryCofan c₁.pt c₂.pt)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (h : IsColimit bc)

/-- For cofans on maps `f₁ : ι₁ → C`, `f₂ : ι₂ → C` and a binary cofan on their
cocone points, construct one family of morphisms indexed by `ι₁ ⊕ ι₂` -/
@[simp]
/-
**CategoryTheory.Limits.Cofan.combPairHoms** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Cofan`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{u₂, u₁} C] →     {ι₁ : 
Type u_1} →       {ι₂ : Type u_2} →         {f₁ : ι₁ → C} →           {f₂ : ι₂ →
 C} →             (c₁ : CategoryTheory.Limits.Cofan f₁) →               (c₂ : Ca
tegoryTheory.Limits.Cofan f₂) →                 (bc : CategoryTheory.Limits.Bina
ryCofan c₁.pt c₂.pt) → (i : ι₁ ⊕ ι₂) → Sum.elim f₁ f₂ i ⟶ bc.pt
参数：c₁ : CategoryTheory.Limits.Cofan f₁；c₂ : CategoryTheory.Limits.Cofan f₂；bc : 
CategoryTheory.Limits.BinaryCofan c₁.pt c₂.pt；i : ι₁ ⊕ ι₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For cofans on maps `f₁ : ι₁ → C`, `f₂ : ι₂ → C` and a binary cofan on their
cocone points, construct one family of morphisms indexed by `ι₁ ⊕ ι₂`
-/
abbrev combPairHoms : (i : ι₁ ⊕ ι₂) → Sum.elim f₁ f₂ i ⟶ bc.pt
  | .inl a => c₁.inj a ≫ bc.inl
  | .inr a => c₂.inj a ≫ bc.inr

variable {c₁ c₂ bc}

set_option backward.isDefEq.respectTransparency false in
/-- If `c₁` and `c₂` are colimit cofans and `bc` is a colimit binary cofan on their cocone
points, then the cofan constructed from `combPairHoms` is a colimit cocone. -/
/-
**CategoryTheory.Limits.Cofan.combPairIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.Cofan`。
形式化陈述：combPairIsColimit : IsColimit (Cofan.mk bc.pt (combPairHoms c₁ c₂ bc))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `c₁` and `c₂` are colimit cofans and `bc` is a colimit binary cofan on their 
cocone
points, then the cofan constructed from `combPairHoms` is a colimit cocone.
-/
def combPairIsColimit : IsColimit (Cofan.mk bc.pt (combPairHoms c₁ c₂ bc)) :=
  Cofan.IsColimit.mk _
    (fun s ↦ Cofan.IsColimit.desc h <| fun i ↦ by
      cases i
      · exact Cofan.IsColimit.desc h₁ (fun a ↦ s.inj (.inl a))
      · exact Cofan.IsColimit.desc h₂ (fun a ↦ s.inj (.inr a)))
    (fun s w ↦ by
      cases w <;>
      · simp only [cofan_mk_inj, combPairHoms, Category.assoc]
        erw [h.fac]
        simp only [Cofan.mk_ι_app, Cofan.IsColimit.fac])
    (fun s m hm ↦ Cofan.IsColimit.hom_ext h _ _ <| fun w ↦ by
      cases w
      · refine Cofan.IsColimit.hom_ext h₁ _ _ (fun a ↦ by aesop)
      · refine Cofan.IsColimit.hom_ext h₂ _ _ (fun a ↦ by aesop))

end Cofan

end Limits

end CategoryTheory

