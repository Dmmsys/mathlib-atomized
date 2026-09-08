/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Properties of objects that are bounded by a cardinal

Given `P : ObjectProperty C` and `κ : Cardinal`, we introduce a predicate
`P.HasCardinalLT κ` saying that the cardinality of `Subtype P` is `< κ`.

-/

public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

/-- The property that the subtype of objects satisfying a property `P : ObjectProperty C`
is of cardinality `< κ`. -/
/-
**CategoryTheory.ObjectProperty.HasCardinalLT** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
ObjectProperty C → Cardinal.{w} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that the subtype of objects satisfying a property `P : ObjectProper
ty C`
is of cardinality `< κ`.
-/
protected abbrev HasCardinalLT (P : ObjectProperty C) (κ : Cardinal.{w}) :=
    _root_.HasCardinalLT (Subtype P) κ
/-
**CategoryTheory.ObjectProperty.hasCardinalLT_subtype_ofObj** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：hasCardinalLT_subtype_ofObj {ι : Type*} (X : ι -> C) {κ : Cardinal.{w}} (h
 : HasCardinalLT ι κ) : (ObjectProperty.ofObj X).HasCardinalLT κ
参数：X : ι -> C；h : HasCardinalLT ι κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasCardinalLT.of_surjective`：of_surjective (f : X -> Y) (hf : Function.S
urjective f) : HasCardinalLT Y κ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma hasCardinalLT_subtype_ofObj
    {ι : Type*} (X : ι → C) {κ : Cardinal.{w}}
    (h : HasCardinalLT ι κ) : (ObjectProperty.ofObj X).HasCardinalLT κ :=
  h.of_surjective (fun i ↦ ⟨X i, by simp⟩) (by rintro ⟨_, ⟨i⟩⟩; exact ⟨i, rfl⟩)
/-
**CategoryTheory.ObjectProperty.HasCardinalLT.iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.ObjectProperty.HasCardinalLT`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} {P
 : ι → CategoryTheory.ObjectProperty C}   {κ : Cardinal.{w}} [Fact κ.IsRegular],
   (∀ (i : ι), (P i).HasCardinalLT κ) → HasCardinalLT ι κ → (⨆ i, P i).HasCardin
alLT κ
参数：∀ (i : ι), (P i).HasCardinalLT κ；⨆ i, P i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasCardinalLT_subtype_iSup`：hasCardinalLT_subtype_iSup {ι : Type*} {X : 
Type*} (P : ι -> X -> Prop) {κ : Cardinal} [Fact κ.IsRegular] (hι : HasCardinalL
T ι κ) (hP : for…
-/
lemma HasCardinalLT.iSup
    {ι : Type*} {P : ι → ObjectProperty C} {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hP : ∀ i, (P i).HasCardinalLT κ) (hι : HasCardinalLT ι κ) :
    (⨆ i, P i).HasCardinalLT κ :=
  hasCardinalLT_subtype_iSup _ hι hP
/-
**CategoryTheory.ObjectProperty.HasCardinalLT.sup** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.ObjectProperty.HasCardinalLT`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P₁ P₂ : Category
Theory.ObjectProperty C} {κ : Cardinal.{w}},   P₁.HasCardinalLT κ → P₂.HasCardin
alLT κ → Cardinal.aleph0 ≤ κ → (P₁ ⊔ P₂).HasCardinalLT κ
参数：P₁ ⊔ P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasCardinalLT_union`：hasCardinalLT_union {X : Type*} {S₁ S₂ : Set X} {κ 
: Cardinal} (hκ : Cardinal.aleph0 <= κ) (h₁ : HasCardinalLT S₁ κ) (h₂ : HasCardi
nalLT S₂ …
-/
lemma HasCardinalLT.sup
    {P₁ P₂ : ObjectProperty C} {κ : Cardinal.{w}}
    (h₁ : P₁.HasCardinalLT κ) (h₂ : P₂.HasCardinalLT κ)
    (hκ : Cardinal.aleph0 ≤ κ) :
    (P₁ ⊔ P₂).HasCardinalLT κ :=
  hasCardinalLT_union hκ h₁ h₂

end ObjectProperty

end CategoryTheory

