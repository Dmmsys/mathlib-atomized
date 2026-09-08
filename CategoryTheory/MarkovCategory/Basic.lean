/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Markov Categories

Copy-discard categories where deletion is natural for all morphisms.

## Main definitions

* `MarkovCategory` - Copy-discard category with natural deletion

## Main results

* `eq_discard` - Any morphism to the unit equals discard
* `isTerminalUnit` - The monoidal unit is terminal

## Implementation notes

Natural discard forces probabilistic interpretation: morphisms preserve normalization. The unit
being terminal follows from naturality of discard.

The key property `discard_natural : f ≫ ε[Y] = ε[X]` means discard "erases" any preceding
morphism, a distinguishing feature of Markov categories in categorical probability.

## References

* [Cho and Jacobs, *Disintegration and Bayesian inversion via string diagrams*][cho_jacobs_2019]
* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

Markov category, probability, categorical probability
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory CopyDiscardCategory ComonObj Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- Copy-discard category where discard is natural. -/
/-
**CategoryTheory.MarkovCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.MonoidalCategory C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy-discard category where discard is natural.
-/
class MarkovCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
    extends CopyDiscardCategory C where
  /-- Process then discard equals discard directly. -/
  discard_natural {X Y : C} (f : X ⟶ Y) : f ≫ ε[Y] = ε[X]

namespace MarkovCategory

variable [MarkovCategory C]

attribute [reassoc (attr := simp)] discard_natural

/-- Any morphism to the unit equals discard. -/
/-
**CategoryTheory.MarkovCategory.eq_discard** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.MarkovCategory`。
形式化陈述：eq_discard (X : C) (f : X ⟶ 𝟙_ C) : f = ε[X]
参数：X : C；f : X ⟶ 𝟙_ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.CopyDiscardCategory.discard_unit`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}  
 [self : CategoryTheory.CopyDiscardCa…
· 使用定理 `CategoryTheory.MarkovCategory.discard_natural`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}   [
self : CategoryTheory.MarkovCategor…

--- 原说明 ---
Any morphism to the unit equals discard.
-/
theorem eq_discard (X : C) (f : X ⟶ 𝟙_ C) : f = ε[X] := by
  rw [← Category.comp_id f, ← discard_unit, discard_natural]

/-- The monoidal unit is a terminal object. -/
/-
**CategoryTheory.MarkovCategory.isTerminalUnit** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.MarkovCategory`。
形式化陈述：isTerminalUnit : IsTerminal (𝟙_ C)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MarkovCategory.eq_discard`：eq_discard (X : C) (f : X ⟶ 𝟙_
 C) : f = ε[X]

--- 原说明 ---
The monoidal unit is a terminal object.
-/
def isTerminalUnit : IsTerminal (𝟙_ C) :=
  IsTerminal.ofUniqueHom _ eq_discard

/-- There is a unique morphism to the unit (it is terminal). -/
/-
**CategoryTheory.MarkovCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Marko
vCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a unique morphism to the unit (it is terminal).
-/
instance (X : C) : Subsingleton (X ⟶ 𝟙_ C) where
  allEq := isTerminalUnit.hom_ext

end MarkovCategory

end CategoryTheory

