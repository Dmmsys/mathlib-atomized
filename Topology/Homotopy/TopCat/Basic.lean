/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopies between morphisms in `TopCat`

In this file, we define the type `TopCat.Homotopy` of homotopies
between two morphisms in the category `TopCat`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace TopCat

variable {X Y Z : TopCat.{u}}

/-- A homotopy between morphisms in `TopCat` is a homotopy between
the corresponding continuous maps. -/
/-
**TopCat.Homotopy** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat`。
形式化陈述：Homotopy (f g : X ⟶ Y)
参数：f g : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homotopy between morphisms in `TopCat` is a homotopy between
the corresponding continuous maps.
-/
abbrev Homotopy (f g : X ⟶ Y) := ContinuousMap.Homotopy f.hom g.hom

namespace Homotopy

variable {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂)

/-- The morphism `X ⊗ I ⟶ Y` that is part of a homotopy between two morphisms in `TopCat`. -/
/-
**TopCat.Homotopy.h** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Homotopy`。
形式化陈述：h (H : Homotopy f₀ f₁) : X otimes I ⟶ Y
参数：H : Homotopy f₀ f₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `X ⊗ I ⟶ Y` that is part of a homotopy between two morphisms in `To
pCat`.
-/
def h (H : Homotopy f₀ f₁) : X ⊗ I ⟶ Y :=
  (β_ _ _).hom ≫ ofHom (H.toContinuousMap.comp (ContinuousMap.prodMap I.homeomorph (.id _)))

-- simps generates the wrong apply lemma
@[simp]
/-
**TopCat.Homotopy.h_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Homotopy`。
形式化陈述：h_hom_apply (p : ↑(X otimes I)) : F.h p = F (I.homeomorph p.2, p.1)
参数：p : ↑(X otimes I)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem h_hom_apply (p : ↑(X ⊗ I)) : F.h p = F (I.homeomorph p.2, p.1) := rfl

@[reassoc (attr := simp)]
/-
**TopCat.Homotopy.** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_h : ι₀ ≫ F.h = f₀ := by
  ext x
  exact F.map_zero_left x

@[reassoc (attr := simp)]
/-
**TopCat.Homotopy.** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_h : ι₁ ≫ F.h = f₁ := by
  ext x
  exact F.map_one_left x

/-- The identity homotopy of a morphism `f : X ⟶ Y` in `TopCat`. -/
/-
**TopCat.Homotopy.refl** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat.Homotopy`。
形式化陈述：refl (f : X ⟶ Y)
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity homotopy of a morphism `f : X ⟶ Y` in `TopCat`.
-/
abbrev refl (f : X ⟶ Y) := ContinuousMap.Homotopy.refl f.hom

@[simp]
/-
**TopCat.Homotopy.h_refl** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Homotopy`。
形式化陈述：h_refl : h (refl f₀) = fst _ _ ≫ f₀
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma h_refl : h (refl f₀) = fst _ _ ≫ f₀ := rfl

/-- The reverse of a homotopy `F` in `TopCat`. -/
/-
**TopCat.Homotopy.symm** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat.Homotopy`。
形式化陈述：symm
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reverse of a homotopy `F` in `TopCat`.
-/
abbrev symm := ContinuousMap.Homotopy.symm F

@[simp]
/-
**TopCat.Homotopy.h_symm** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Homotopy`。
形式化陈述：h_symm : h F.symm = (X ◁ I.symm) ≫ F.h
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma h_symm : h F.symm = (X ◁ I.symm) ≫ F.h := rfl

/-- The compositions of homotopies in `TopCat`. -/
/-
**TopCat.Homotopy.trans** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat.Homotopy`。
形式化陈述：trans
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The compositions of homotopies in `TopCat`.
-/
noncomputable abbrev trans := ContinuousMap.Homotopy.trans F G

/-- The homotopy between compositions of morphisms in `TopCat`. -/
@[simps!]
/-
**TopCat.Homotopy.comp** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat.Homotopy`。
形式化陈述：comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀
 f₁) : Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁)
参数：G : Homotopy g₀ g₁；F : Homotopy f₀ f₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy between compositions of morphisms in `TopCat`.
-/
abbrev comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
    Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁) := ContinuousMap.Homotopy.comp G F

attribute [nolint simpNF] comp_apply

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**TopCat.Homotopy.h_comp** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Homotopy`。
形式化陈述：h_comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy 
f₀ f₁) : (G.comp F).h = X ◁ lift (𝟙 I) (𝟙 I) ≫ (α_ _ _ _).inv ≫ F.h ▷ _ ≫ G.h
参数：G : Homotopy g₀ g₁；F : Homotopy f₀ f₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.ext`：ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (w : forall x : X, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Homotopy.comp_apply`：∀ {X Y Z : TopCat} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : 
Y ⟶ Z} (G : TopCat.Homotopy g₀ g₁) (F : TopCat.Homotopy f₀ f₁)   (x : ↑unitInter
val × ↑X), (G.co…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma h_comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
    (G.comp F).h = X ◁ lift (𝟙 I) (𝟙 I) ≫ (α_ _ _ _).inv ≫ F.h ▷ _ ≫ G.h := by
  ext
  simp

end Homotopy

end TopCat

