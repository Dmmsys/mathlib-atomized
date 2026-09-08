/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# The retract argument

Let `W₁` and `W₂` be classes of morphisms in a category `C` such that
any morphism can be factored as a morphism in `W₁` followed by
a morphism in `W₂` (this is `HasFactorization W₁ W₂`).
If `W₁` has the left lifting property with respect to `W₂`
(i.e. `W₁ ≤ W₂.llp`, or equivalently `W₂ ≤ W₁.rlp`),
then `W₂.llp = W₁` if `W₁` is stable under retracts,
and `W₁.rlp = W₂` if `W₂` is.

## Reference
- https://ncatlab.org/nlab/show/weak+factorization+system#retract_argument

-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C]

set_option backward.defeqAttrib.useBackward true in
/-- If `i ≫ p = f`, and `f` has the left lifting property with respect to `p`,
then `f` is a retract of `i`. -/
/-
**CategoryTheory.RetractArrow.ofLeftLiftingProperty** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.RetractArrow`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y Z : C} →       {f : X ⟶ Z} →         {i : X ⟶ Y} →           {p : Y ⟶ Z} →    
         CategoryTheory.CategoryStruct.comp i p = f →               [CategoryThe
ory.HasLiftingProperty f p] → CategoryTheory.RetractArrow f i
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i ≫ p = f`, and `f` has the left lifting property with respect to `p`,
then `f` is a retract of `i`.
-/
noncomputable def RetractArrow.ofLeftLiftingProperty
    {X Y Z : C} {f : X ⟶ Z} {i : X ⟶ Y} {p : Y ⟶ Z} (h : i ≫ p = f)
    [HasLiftingProperty f p] : RetractArrow f i :=
  have sq : CommSq i f p (𝟙 _) := ⟨by simp [h]⟩
  { i := Arrow.homMk (𝟙 X) sq.lift
    r := Arrow.homMk (𝟙 X) p }

set_option backward.defeqAttrib.useBackward true in
/-- If `i ≫ p = f`, and `f` has the right lifting property with respect to `i`,
then `f` is a retract of `p`. -/
/-
**CategoryTheory.RetractArrow.ofRightLiftingProperty** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.RetractArrow`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y Z : C} →       {f : X ⟶ Z} →         {i : X ⟶ Y} →           {p : Y ⟶ Z} →    
         CategoryTheory.CategoryStruct.comp i p = f →               [CategoryThe
ory.HasLiftingProperty i f] → CategoryTheory.RetractArrow f p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i ≫ p = f`, and `f` has the right lifting property with respect to `i`,
then `f` is a retract of `p`.
-/
noncomputable def RetractArrow.ofRightLiftingProperty
    {X Y Z : C} {f : X ⟶ Z} {i : X ⟶ Y} {p : Y ⟶ Z} (h : i ≫ p = f)
    [HasLiftingProperty i f] : RetractArrow f p :=
  have sq : CommSq (𝟙 _) i f p := ⟨by simp [h]⟩
  { i := Arrow.homMk i (𝟙 _)
    r := Arrow.homMk sq.lift (𝟙 _) }

namespace MorphismProperty

variable {W₁ W₂ : MorphismProperty C}

/-
**CategoryTheory.MorphismProperty.llp_eq_of_le_llp_of_hasFactorization_of_isStab
leUnderRetracts** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts [HasFactoriz
ation W₁ W₂] [W₁.IsStableUnderRetracts] (h₁ : W₁ <= W₂.llp) : W₂.llp = W₁
参数：h₁ : W₁ <= W₂.llp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hp`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用引理 `CategoryTheory.MorphismProperty.of_retract`：of_retract {P : MorphismProp
erty C} [P.IsStableUnderRetracts] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : Ret
ractArrow f g) (hg : P g) : P f
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphis
mProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hi`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
-/
lemma llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts
    [HasFactorization W₁ W₂] [W₁.IsStableUnderRetracts] (h₁ : W₁ ≤ W₂.llp) :
    W₂.llp = W₁ :=
  le_antisymm (fun A B i hi ↦ by
    have h := factorizationData W₁ W₂ i
    have := hi _ h.hp
    simpa using of_retract (RetractArrow.ofLeftLiftingProperty h.fac) h.hi) h₁
/-
**CategoryTheory.MorphismProperty.rlp_eq_of_le_rlp_of_hasFactorization_of_isStab
leUnderRetracts** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts [HasFactoriz
ation W₁ W₂] [W₂.IsStableUnderRetracts] (h₂ : W₂ <= W₁.rlp) : W₁.rlp = W₂
参数：h₂ : W₂ <= W₁.rlp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hi`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用引理 `CategoryTheory.MorphismProperty.of_retract`：of_retract {P : MorphismProp
erty C} [P.IsStableUnderRetracts] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : Ret
ractArrow f g) (hg : P g) : P f
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphis
mProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hp`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
-/
lemma rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts
    [HasFactorization W₁ W₂] [W₂.IsStableUnderRetracts] (h₂ : W₂ ≤ W₁.rlp) :
    W₁.rlp = W₂ :=
  le_antisymm (fun X Y p hp ↦ by
    have h := factorizationData W₁ W₂ p
    have := hp _ h.hi
    simpa using of_retract (RetractArrow.ofRightLiftingProperty h.fac) h.hp) h₂

end MorphismProperty

end CategoryTheory

