/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.EpiMono

/-!
# Balanced categories

A category is called balanced if any morphism that is both monic and epic is an isomorphism.

Balanced categories arise frequently. For example, categories in which every monomorphism
(or epimorphism) is strong are balanced. Examples of this are abelian categories and toposes, such
as the category of types.

-/

public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- A category is called balanced if any morphism that is both monic and epic is an isomorphism. -/
/-
**CategoryTheory.Balanced** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：Balanced : Prop where isIso_of_mono_of_epi : forall {X Y : C} (f : X ⟶ Y) 
[Mono f] [Epi f], IsIso f  attribute [to_dual self (reorder
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is called balanced if any morphism that is both monic and epic is an 
isomorphism.
-/
class Balanced : Prop where
  isIso_of_mono_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f], IsIso f

attribute [to_dual self (reorder := X Y, 7 8)] Balanced.isIso_of_mono_of_epi
attribute [to_dual self (reorder := isIso_of_mono_of_epi (X Y, 4 5))] Balanced.mk

@[to_dual self (reorder := X Y, 7 8)]
/-
**CategoryTheory.isIso_of_mono_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：isIso_of_mono_of_epi [Balanced C] {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] :
 IsIso f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Balanced.isIso_of_mono_of_epi`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.Balanced C] {X Y : C} (f :
 X ⟶ Y)   [CategoryTheory.Mono f] …
-/
theorem isIso_of_mono_of_epi [Balanced C] {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f :=
  Balanced.isIso_of_mono_of_epi _

@[to_dual isIso_iff_epi_and_mono]
/-
**CategoryTheory.isIso_iff_mono_and_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：isIso_iff_mono_and_epi [Balanced C] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Mono
 f ∧ Epi f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
-/
theorem isIso_iff_mono_and_epi [Balanced C] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Mono f ∧ Epi f :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => isIso_of_mono_of_epi _⟩

section

attribute [local instance] isIso_of_mono_of_epi

/-
**CategoryTheory.balanced_opposite** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：balanced_opposite [Balanced C] : Balanced Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quiver.Hom.op_unop`：Quiver.Hom.op_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.unop.
op = f
· 使用定理 `CategoryTheory.isIso_of_op`：isIso_of_op {X Y : C} (f : X ⟶ Y) [IsIso f.o
p] : IsIso f
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `CategoryTheory.unop_mono_of_epi`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {A B : Cᵒᵖ} (f : B ⟶ A) [CategoryTheory.Epi f],   CategoryT
heory.Mono f.unop
-/
instance balanced_opposite [Balanced C] : Balanced Cᵒᵖ :=
  { isIso_of_mono_of_epi := fun f fmono fepi => by
      rw [← Quiver.Hom.op_unop f]
      exact isIso_of_op _ }

end

end CategoryTheory

