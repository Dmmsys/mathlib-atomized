/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# Strict bicategories

A bicategory is called `Strict` if the left unitors, the right unitors, and the associators are
isomorphisms given by equalities.

## Implementation notes

In the literature of category theory, a strict bicategory (usually called a strict 2-category) is
often defined as a bicategory whose left unitors, right unitors, and associators are identities.
We cannot use this definition directly here since the types of 2-morphisms depend on 1-morphisms.
For this reason, we use `eqToIso`, which gives isomorphisms from equalities, instead of
identities.
-/

public section


namespace CategoryTheory

open Bicategory

universe w v u

variable (B : Type u) [Bicategory.{w, v} B]

/-- A bicategory is called `Strict` if the left unitors, the right unitors, and the associators are
isomorphisms given by equalities.
-/
/-
**CategoryTheory.Bicategory.Strict** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.B
icategory`。
形式化陈述：(B : Type u) → [CategoryTheory.Bicategory B] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bicategory is called `Strict` if the left unitors, the right unitors, and the 
associators are
isomorphisms given by equalities.
-/
class Bicategory.Strict : Prop where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {a b : B} (f : a ⟶ b), 𝟙 a ≫ f = f := by cat_disch
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {a b : B} (f : a ⟶ b), f ≫ 𝟙 b = f := by cat_disch
  /-- Composition in a bicategory is associative. -/
  assoc : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    cat_disch
  /-- The left unitors are given by equalities -/
  leftUnitor_eqToIso : ∀ {a b : B} (f : a ⟶ b), λ_ f = eqToIso (id_comp f) := by cat_disch
  /-- The right unitors are given by equalities -/
  rightUnitor_eqToIso : ∀ {a b : B} (f : a ⟶ b), ρ_ f = eqToIso (comp_id f) := by cat_disch
  /-- The associators are given by equalities -/
  associator_eqToIso :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), α_ f g h = eqToIso (assoc f g h) := by
    cat_disch

-- see Note [lower instance priority]
/-- Category structure on a strict bicategory -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category structure on a strict bicategory
-/
instance (priority := 100) StrictBicategory.category [Bicategory.Strict B] : Category B where
  id_comp := Bicategory.Strict.id_comp
  comp_id := Bicategory.Strict.comp_id
  assoc := Bicategory.Strict.assoc

namespace Bicategory

variable {B}

@[simp]
/-
**CategoryTheory.Bicategory.whiskerLeft_eqToHom** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Bicategory`。
形式化陈述：whiskerLeft_eqToHom {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g = h) : f 
◁ eqToHom η = eqToHom (congr_arg₂ (· ≫ ·) rfl η)
参数：f : a ⟶ b；η : g = h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_id`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bica
tegory.whiskerLeft f (Category…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem whiskerLeft_eqToHom {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g = h) :
    f ◁ eqToHom η = eqToHom (congr_arg₂ (· ≫ ·) rfl η) := by
  cases η
  simp only [whiskerLeft_id, eqToHom_refl]

@[simp]
/-
**CategoryTheory.Bicategory.eqToHom_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：eqToHom_whiskerRight {a b c : B} {f g : a ⟶ b} (η : f = g) (h : b ⟶ c) : e
qToHom η ▷ h = eqToHom (congr_arg₂ (· ≫ ·) η rfl)
参数：η : f = g；h : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.id_whiskerRight`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bic
ategory.whiskerRight (CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem eqToHom_whiskerRight {a b c : B} {f g : a ⟶ b} (η : f = g) (h : b ⟶ c) :
    eqToHom η ▷ h = eqToHom (congr_arg₂ (· ≫ ·) η rfl) := by
  cases η
  simp only [id_whiskerRight, eqToHom_refl]

end Bicategory

end CategoryTheory

