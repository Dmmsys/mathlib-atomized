/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.LiftingProperties.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# The model category structure on Over categories

Let `C` be a model category. For any `S : C`, we define
a model category structure on the category `Over S`:
a morphism `X ⟶ Y` in `Over S` is a cofibration
(resp. a fibration, a weak equivalence) if the
underlying morphism `f.left : X.left ⟶ Y.left` is.
(Apart from the existence of (finite) limits
from `Mathlib.CategoryTheory.Limits.Constructions.Over.Basic`, the verification
of the axioms is straightforward.)

## TODO
* Proceed to the dual construction for `Under S`.

-/

@[expose] public section

universe v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] (S : C)

namespace HomotopicalAlgebra

section

variable [CategoryWithCofibrations C]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CategoryWithCofibrations (Over S) where
  cofibrations := (cofibrations C).over
/-
**HomotopicalAlgebra.cofibrations_over_def** 是 Mathlib 中的一个引理，位于命名空间 `Homotopica
lAlgebra`。
形式化陈述：cofibrations_over_def : cofibrations (Over S) = (cofibrations C).over
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cofibrations_over_def :
    cofibrations (Over S) = (cofibrations C).over := rfl
/-
**HomotopicalAlgebra.cofibrations_over_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homotopica
lAlgebra`。
形式化陈述：cofibrations_over_iff {X Y : Over S} (f : X ⟶ Y) : Cofibration f ↔ Cofibra
tion f.left
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cofibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.left := by
  simp only [cofibration_iff, cofibrations_over_def, MorphismProperty.over_iff]
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Over S} (f : X ⟶ Y) [Cofibration f] : Cofibration f.left := by
  rwa [← cofibrations_over_iff]
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(cofibrations C).IsStableUnderRetracts] :
    (cofibrations (Over S)).IsStableUnderRetracts := by
  rw [cofibrations_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithFibrations C]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CategoryWithFibrations (Over S) where
  fibrations := (fibrations C).over
/-
**HomotopicalAlgebra.fibrations_over_def** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalA
lgebra`。
形式化陈述：fibrations_over_def : fibrations (Over S) = (fibrations C).over
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fibrations_over_def :
    fibrations (Over S) = (fibrations C).over := rfl
/-
**HomotopicalAlgebra.fibrations_over_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalA
lgebra`。
形式化陈述：fibrations_over_iff {X Y : Over S} (f : X ⟶ Y) : Fibration f ↔ Fibration f
.left
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma fibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.left := by
  simp only [fibration_iff, fibrations_over_def, MorphismProperty.over_iff]
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Over S} (f : X ⟶ Y) [Fibration f] : Fibration f.left := by
  rwa [← fibrations_over_iff]
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(fibrations C).IsStableUnderRetracts] :
    (fibrations (Over S)).IsStableUnderRetracts := by
  rw [fibrations_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithWeakEquivalences C]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CategoryWithWeakEquivalences (Over S) where
  weakEquivalences := (weakEquivalences C).over
/-
**HomotopicalAlgebra.weakEquivalences_over_def** 是 Mathlib 中的一个引理，位于命名空间 `Homoto
picalAlgebra`。
形式化陈述：weakEquivalences_over_def : weakEquivalences (Over S) = (weakEquivalences 
C).over
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weakEquivalences_over_def :
    weakEquivalences (Over S) = (weakEquivalences C).over := rfl
/-
**HomotopicalAlgebra.weakEquivalences_over_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homoto
picalAlgebra`。
形式化陈述：weakEquivalences_over_iff {X Y : Over S} (f : X ⟶ Y) : WeakEquivalence f ↔
 WeakEquivalence f.left
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma weakEquivalences_over_iff {X Y : Over S} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.left := by
  simp only [weakEquivalence_iff, weakEquivalences_over_def, MorphismProperty.over_iff]
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Over S} (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence f.left := by
  rwa [← weakEquivalences_over_iff]
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(weakEquivalences C).IsStableUnderRetracts] :
    (weakEquivalences (Over S)).IsStableUnderRetracts := by
  rw [weakEquivalences_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

end

/-
**HomotopicalAlgebra.trivialCofibrations_over_eq** 是 Mathlib 中的一个引理，位于命名空间 `Homo
topicalAlgebra`。
形式化陈述：trivialCofibrations_over_eq [CategoryWithWeakEquivalences C] [CategoryWith
Cofibrations C] : trivialCofibrations (Over S) = (trivialCofibrations C).over
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trivialCofibrations_over_eq
    [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C] :
    trivialCofibrations (Over S) = (trivialCofibrations C).over := rfl
/-
**HomotopicalAlgebra.trivialFibrations_over_eq** 是 Mathlib 中的一个引理，位于命名空间 `Homoto
picalAlgebra`。
形式化陈述：trivialFibrations_over_eq [CategoryWithWeakEquivalences C] [CategoryWithFi
brations C] : trivialFibrations (Over S) = (trivialFibrations C).over
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trivialFibrations_over_eq
    [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] :
    trivialFibrations (Over S) = (trivialFibrations C).over := rfl
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CategoryWithWeakEquivalences C]
    [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences (Over S)).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

section

variable [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]
  [CategoryWithFibrations C]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(trivialCofibrations C).HasFactorization (fibrations C)] :
    (trivialCofibrations (Over S)).HasFactorization (fibrations (Over S)) := by
  rw [fibrations_over_def, trivialCofibrations_over_eq]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(cofibrations C).HasFactorization (trivialFibrations C)] :
    (cofibrations (Over S)).HasFactorization (trivialFibrations (Over S)) := by
  rw [cofibrations_over_def, trivialFibrations_over_eq]
  infer_instance

end

/-
**HomotopicalAlgebra.ModelCategory.over** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAl
gebra.ModelCategory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (S : C) →
 [HomotopicalAlgebra.ModelCategory C] → HomotopicalAlgebra.ModelCategory (Catego
ryTheory.Over S)
参数：S : C；CategoryTheory.Over S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ModelCategory.over [ModelCategory C] : ModelCategory (Over S) where
  cm4a _ _ _ _ _ := .over _ _
  cm4b _ _ _ _ _ := .over _ _

end HomotopicalAlgebra

