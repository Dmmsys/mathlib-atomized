/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Characterization of projective objects in terms of lifting properties

An object `P` is projective iff the morphism `0 ⟶ P` has the
left lifting property with respect to epimorphisms,
`projective_iff_llp_epimorphisms_zero`.

-/

public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C]

namespace Projective

/-
**CategoryTheory.Projective.hasLiftingProperty_of_isZero** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Projective`。
形式化陈述：hasLiftingProperty_of_isZero {Z P X Y : C} (i : Z ⟶ P) (p : X ⟶ Y) [Epi p]
 [Projective P] (hZ : IsZero Z) : HasLiftingProperty i p where sq_hasLift {f g} 
sq
参数：i : Z ⟶ P；p : X ⟶ Y；hZ : IsZero Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Projective.factorThru_comp`：factorThru_comp {P X E : C} [
Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : factorThru f e ≫ e = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hasLiftingProperty_of_isZero
    {Z P X Y : C} (i : Z ⟶ P) (p : X ⟶ Y) [Epi p] [Projective P] (hZ : IsZero Z) :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := ⟨⟨{
    l := Projective.factorThru g p
    fac_left := hZ.eq_of_src _ _ }⟩⟩
/-
**CategoryTheory.Projective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Projectiv
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y P : C} (p : X ⟶ Y) [Epi p] [Projective P] [HasZeroObject C] (i : 0 ⟶ P) :
    HasLiftingProperty (i : 0 ⟶ P) p :=
  Projective.hasLiftingProperty_of_isZero i p (isZero_zero C)

end Projective

/-
**CategoryTheory.projective_iff_llp_epimorphisms_of_isZero** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory`。
形式化陈述：projective_iff_llp_epimorphisms_of_isZero [HasZeroMorphisms C] {P Z : C} (
i : Z ⟶ P) (hZ : IsZero Z) : Projective P ↔ (MorphismProperty.epimorphisms C).ll
p i
参数：i : Z ⟶ P；hZ : IsZero Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Projective.hasLiftingProperty_of_isZero`：hasLiftingProper
ty_of_isZero {Z P X Y : C} (i : Z ⟶ P) (p : X ⟶ Y) [Epi p] [Projective P] (hZ : 
IsZero Z) : HasLiftingProperty i p where sq_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.CommSq.fac_right`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X}   {g :
 Y ⟶ B} (sq : Categor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
-/
lemma projective_iff_llp_epimorphisms_of_isZero
    [HasZeroMorphisms C] {P Z : C} (i : Z ⟶ P) (hZ : IsZero Z) :
    Projective P ↔ (MorphismProperty.epimorphisms C).llp i := by
  obtain rfl := hZ.eq_of_src i 0
  constructor
  · intro _ X Y p (_ : Epi p)
    exact Projective.hasLiftingProperty_of_isZero 0 p hZ
  · intro h
    constructor
    intro X Y f p hp
    have := h _ hp
    have sq : CommSq 0 (0 : Z ⟶ P) p f := ⟨by simp⟩
    exact ⟨sq.lift, by simp⟩
/-
**CategoryTheory.projective_iff_llp_epimorphisms_zero** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory`。
形式化陈述：projective_iff_llp_epimorphisms_zero [HasZeroMorphisms C] [HasZeroObject C
] (P : C) : Projective P ↔ (MorphismProperty.epimorphisms C).llp (0 : 0 ⟶ P)
参数：P : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.projective_iff_llp_epimorphisms_of_isZero`：projective_iff
_llp_epimorphisms_of_isZero [HasZeroMorphisms C] {P Z : C} (i : Z ⟶ P) (hZ : IsZ
ero Z) : Projective P ↔ (MorphismProperty.epim…
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
-/
lemma projective_iff_llp_epimorphisms_zero
    [HasZeroMorphisms C] [HasZeroObject C] (P : C) :
    Projective P ↔ (MorphismProperty.epimorphisms C).llp (0 : 0 ⟶ P) :=
  projective_iff_llp_epimorphisms_of_isZero _ (isZero_zero C)

end CategoryTheory

