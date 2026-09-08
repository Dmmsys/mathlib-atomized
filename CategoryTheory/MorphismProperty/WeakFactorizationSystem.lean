/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.RetractArgument

/-!
# Weak factorization systems

In this file, we introduce the notion of weak factorization system,
which is a property of two classes of morphisms `W₁` and `W₂` in
a category `C`. The type class `IsWeakFactorizationSystem W₁ W₂` asserts
that `W₁` is exactly `W₂.llp`, `W₂` is exactly `W₁.rlp`,
and any morphism in `C` can be factored a `i ≫ p` with `W₁ i` and `W₂ p`.

## References
* https://ncatlab.org/nlab/show/weak+factorization+system

-/

public section

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (W₁ W₂ : MorphismProperty C)

/-- Two classes of morphisms `W₁` and `W₂` in a category `C` form a weak
factorization system if `W₁` is exactly `W₂.llp`, `W₂` is exactly `W₁.rlp`,
and any morphism can be factored a `i ≫ p` with `W₁ i` and `W₂ p`. -/
/-
**CategoryTheory.MorphismProperty.IsWeakFactorizationSystem** 是 Mathlib 中的一个类，位于
命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：IsWeakFactorizationSystem : Prop where rlp : W₁.rlp = W₂ llp : W₂.llp = W₁
 hasFactorization : HasFactorization W₁ W₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two classes of morphisms `W₁` and `W₂` in a category `C` form a weak
factorization system if `W₁` is exactly `W₂.llp`, `W₂` is exactly `W₁.rlp`,
and any morphism can be factored a `i ≫ p` with `W₁ i` and `W₂ p`.
-/
class IsWeakFactorizationSystem : Prop where
  rlp : W₁.rlp = W₂
  llp : W₂.llp = W₁
  hasFactorization : HasFactorization W₁ W₂ := by infer_instance

namespace IsWeakFactorizationSystem

attribute [instance] hasFactorization

/-
**CategoryTheory.MorphismProperty.IsWeakFactorizationSystem.mk'** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.MorphismProperty.IsWeakFactorizationSystem`。
形式化陈述：mk' [HasFactorization W₁ W₂] [W₁.IsStableUnderRetracts] [W₂.IsStableUnderR
etracts] (h : forall {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y), W₁ i -> W₂ p -> HasL
iftingProperty i p) : IsWeakFactorizationSystem W₁ W₂ where rlp
参数：h : forall {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y), W₁ i -> W₂ p -> HasLiftingP
roperty i p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.rlp_eq_of_le_rlp_of_hasFactorization_of_
isStableUnderRetracts`：rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetr
acts [HasFactorization W₁ W₂] [W₂.IsStableUnderRetracts] (h₂ : W₂ <= W₁.rlp) : W
₁.r…
· 使用引理 `CategoryTheory.MorphismProperty.llp_eq_of_le_llp_of_hasFactorization_of_
isStableUnderRetracts`：llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetr
acts [HasFactorization W₁ W₂] [W₁.IsStableUnderRetracts] (h₁ : W₁ <= W₂.llp) : W
₂.l…
-/
lemma mk' [HasFactorization W₁ W₂]
    [W₁.IsStableUnderRetracts] [W₂.IsStableUnderRetracts]
    (h : ∀ {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y),
      W₁ i → W₂ p → HasLiftingProperty i p) :
    IsWeakFactorizationSystem W₁ W₂ where
  rlp := rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts
    (fun _ _ _ hp _ _ _ hi ↦ h _ _ hi hp)
  llp := llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts
    (fun _ _ _ hi _ _ _ hp ↦ h _ _ hi hp)

end IsWeakFactorizationSystem

section

variable [IsWeakFactorizationSystem W₁ W₂]

/-
**CategoryTheory.MorphismProperty.rlp_eq_of_wfs** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：rlp_eq_of_wfs : W₁.rlp = W₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsWeakFactorizationSystem.rlp`：∀ {C : Ty
pe u} {inst : CategoryTheory.Category.{v, u} C} {W₁ W₂ : CategoryTheory.Morphism
Property C}   [self : W₁.IsWeakFactorizationSystem …
-/
lemma rlp_eq_of_wfs : W₁.rlp = W₂ := IsWeakFactorizationSystem.rlp
/-
**CategoryTheory.MorphismProperty.llp_eq_of_wfs** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：llp_eq_of_wfs : W₂.llp = W₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsWeakFactorizationSystem.llp`：∀ {C : Ty
pe u} {inst : CategoryTheory.Category.{v, u} C} {W₁ W₂ : CategoryTheory.Morphism
Property C}   [self : W₁.IsWeakFactorizationSystem …
-/
lemma llp_eq_of_wfs : W₂.llp = W₁ := IsWeakFactorizationSystem.llp

variable {W₁ W₂} in
/-
**CategoryTheory.MorphismProperty.hasLiftingProperty_of_wfs** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：hasLiftingProperty_of_wfs {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) (hi : W₁ i
) (hp : W₂ p) : HasLiftingProperty i p
参数：i : A ⟶ B；p : X ⟶ Y；hi : W₁ i；hp : W₂ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.llp_eq_of_wfs`：llp_eq_of_wfs : W₂.llp = 
W₁
-/
lemma hasLiftingProperty_of_wfs {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : W₁ i) (hp : W₂ p) : HasLiftingProperty i p :=
  (llp_eq_of_wfs W₁ W₂ ▸ hi) p hp

end

end CategoryTheory.MorphismProperty

