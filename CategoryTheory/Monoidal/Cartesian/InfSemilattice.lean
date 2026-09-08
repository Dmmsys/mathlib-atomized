/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The preorder category of a meet-semilattice with a greatest element is Cartesian monoidal

The preorder category of a meet-semilattice `C` with a greatest element is Cartesian monoidal.

A symmetric monoidal structure on the preorder category is automatically provided by the
instance and `CartesianMonoidalCategory.toSymmetricCategory`.
-/

public section

namespace CategoryTheory

open Category MonoidalCategory

universe u

variable (C : Type u) [SemilatticeInf C] [OrderTop C]

namespace SemilatticeInf

/-- Cartesian monoidal structure for the preorder category of a meet-semilattice with
a greatest element. -/
/-
**CategoryTheory.SemilatticeInf.cartesianMonoidalCategory** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.SemilatticeInf`。
形式化陈述：(C : Type u) → [inst : SemilatticeInf C] → [OrderTop C] → CategoryTheory.C
artesianMonoidalCategory C
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b

--- 原说明 ---
Cartesian monoidal structure for the preorder category of a meet-semilattice wit
h
a greatest element.
-/
noncomputable scoped instance cartesianMonoidalCategory : CartesianMonoidalCategory C :=
  .ofChosenFiniteProducts ⟨_, Preorder.isTerminalTop C⟩ fun X Y ↦ ⟨_, Preorder.isLimitBinaryFan X Y⟩

/-- Braided structure for the preorder category of a meet-semilattice with a greatest element. -/
/-
**CategoryTheory.SemilatticeInf.braidedCategory** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.SemilatticeInf`。
形式化陈述：(C : Type u) → [inst : SemilatticeInf C] → [inst_1 : OrderTop C] → Categor
yTheory.BraidedCategory C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Braided structure for the preorder category of a meet-semilattice with a greates
t element.
-/
noncomputable scoped instance braidedCategory : BraidedCategory C := .ofCartesianMonoidalCategory
/-
**CategoryTheory.SemilatticeInf.tensorObj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.SemilatticeInf`。
形式化陈述：tensorObj {C : Type u} [SemilatticeInf C] [OrderTop C] {X Y : C} : X otime
s Y = X ⊓ Y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj {C : Type u} [SemilatticeInf C] [OrderTop C] {X Y : C} : X ⊗ Y = X ⊓ Y := rfl
/-
**CategoryTheory.SemilatticeInf.tensorUnit** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.SemilatticeInf`。
形式化陈述：tensorUnit {C : Type u} [SemilatticeInf C] [OrderTop C] : 𝟙_ C = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit {C : Type u} [SemilatticeInf C] [OrderTop C] :
    𝟙_ C = ⊤ := rfl

end SemilatticeInf

end CategoryTheory

