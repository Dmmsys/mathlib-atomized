/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Instances
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Fibrant and cofibrant objects in a model category

Once a category `C` has been endowed with a `CategoryWithCofibrations C`
instance, it is possible to define the property `IsCofibrant X` for
any `X : C` as an abbreviation for `Cofibration (initial.to X : ⊥_ C ⟶ X)`.
(Fibrant objects are defined similarly.)

-/

public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C]

section

variable [CategoryWithCofibrations C] [HasInitial C]

/-- An object `X` is cofibrant if `⊥_ C ⟶ X` is a cofibration. -/
/-
**HomotopicalAlgebra.IsCofibrant** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopicalAlgebra
`。
形式化陈述：IsCofibrant (X : C) : Prop
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` is cofibrant if `⊥_ C ⟶ X` is a cofibration.
-/
abbrev IsCofibrant (X : C) : Prop := Cofibration (initial.to X)
/-
**HomotopicalAlgebra.isCofibrant_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlgeb
ra`。
形式化陈述：isCofibrant_iff (X : C) : IsCofibrant X ↔ Cofibration (initial.to X)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isCofibrant_iff (X : C) :
    IsCofibrant X ↔ Cofibration (initial.to X) := Iff.rfl

set_option backward.defeqAttrib.useBackward true in
/-
**HomotopicalAlgebra.isCofibrant_iff_of_isInitial** 是 Mathlib 中的一个引理，位于命名空间 `Hom
otopicalAlgebra`。
形式化陈述：isCofibrant_iff_of_isInitial [(cofibrations C).RespectsIso] {A X : C} (i :
 A ⟶ X) (hA : IsInitial A) : IsCofibrant X ↔ Cofibration i
参数：cofibrations C；i : A ⟶ X；hA : IsInitial A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.Limits.IsInitial.to_comp`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X : C} (t : CategoryTheory.Limits.IsInitial X) {Y 
Z : C}   (f : Y ⟶ Z), Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma isCofibrant_iff_of_isInitial [(cofibrations C).RespectsIso]
    {A X : C} (i : A ⟶ X) (hA : IsInitial A) :
    IsCofibrant X ↔ Cofibration i := by
  simp only [cofibration_iff]
  apply (cofibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (IsInitial.uniqueUpToIso initialIsInitial hA) (Iso.refl _)
/-
**HomotopicalAlgebra.isCofibrant_of_cofibration** 是 Mathlib 中的一个引理，位于命名空间 `Homot
opicalAlgebra`。
形式化陈述：isCofibrant_of_cofibration [(cofibrations C).IsStableUnderComposition] {X 
Y : C} (i : X ⟶ Y) [Cofibration i] [hX : IsCofibrant X] : IsCofibrant Y
参数：cofibrations C；i : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopicalAlgebra.isCofibrant_iff`：isCofibrant_iff (X : C) : IsCofibran
t X ↔ Cofibration (initial.to X)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `HomotopicalAlgebra.instCofibrationCompOfIsStableUnderCompositionCofibrat
ions`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z)   [inst_1 : HomotopicalAlgebra.CategoryWithCofi…
-/
lemma isCofibrant_of_cofibration [(cofibrations C).IsStableUnderComposition]
    {X Y : C} (i : X ⟶ Y) [Cofibration i] [hX : IsCofibrant X] :
    IsCofibrant Y := by
  rw [isCofibrant_iff] at hX ⊢
  rw [Subsingleton.elim (initial.to Y) (initial.to X ≫ i)]
  infer_instance

section

variable (X Y : C) [(cofibrations C).IsStableUnderCobaseChange] [HasBinaryCoproduct X Y]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hY : IsCofibrant Y] :
    Cofibration (coprod.inl : X ⟶ X ⨿ Y) := by
  rw [isCofibrant_iff] at hY
  rw [cofibration_iff] at hY ⊢
  exact MorphismProperty.of_isPushout
    ((IsPushout.of_isColimit_binaryCofan_of_isInitial
    (colimit.isColimit (pair X Y)) initialIsInitial).flip) hY
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hX : IsCofibrant X] : Cofibration (coprod.inr : Y ⟶ X ⨿ Y) := by
  rw [isCofibrant_iff] at hX
  rw [cofibration_iff] at hX ⊢
  exact MorphismProperty.of_isPushout
    (IsPushout.of_isColimit_binaryCofan_of_isInitial
    (colimit.isColimit (pair X Y)) initialIsInitial) hX

end

end

section

variable [CategoryWithFibrations C] [HasTerminal C]

/-- An object `X` is fibrant if `X ⟶ ⊤_ C` is a fibration. -/
/-
**HomotopicalAlgebra.IsFibrant** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：IsFibrant (X : C) : Prop
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` is fibrant if `X ⟶ ⊤_ C` is a fibration.
-/
abbrev IsFibrant (X : C) : Prop := Fibration (terminal.from X)
/-
**HomotopicalAlgebra.isFibrant_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlgebra
`。
形式化陈述：isFibrant_iff (X : C) : IsFibrant X ↔ Fibration (terminal.from X)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isFibrant_iff (X : C) :
    IsFibrant X ↔ Fibration (terminal.from X) := Iff.rfl

set_option backward.defeqAttrib.useBackward true in
/-
**HomotopicalAlgebra.isFibrant_iff_of_isTerminal** 是 Mathlib 中的一个引理，位于命名空间 `Homo
topicalAlgebra`。
形式化陈述：isFibrant_iff_of_isTerminal [(fibrations C).RespectsIso] {X Y : C} (p : X 
⟶ Y) (hY : IsTerminal Y) : IsFibrant X ↔ Fibration p
参数：fibrations C；p : X ⟶ Y；hY : IsTerminal Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `CategoryTheory.Limits.IsTerminal.comp_from`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {Z : C} (t : CategoryTheory.Limits.IsTerminal Z)
 {X Y : C}   (f : X ⟶ Y), Catego…
-/
lemma isFibrant_iff_of_isTerminal [(fibrations C).RespectsIso]
    {X Y : C} (p : X ⟶ Y) (hY : IsTerminal Y) :
    IsFibrant X ↔ Fibration p := by
  simp only [fibration_iff]
  symm
  apply (fibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (IsTerminal.uniqueUpToIso hY terminalIsTerminal)
/-
**HomotopicalAlgebra.isFibrant_of_fibration** 是 Mathlib 中的一个引理，位于命名空间 `Homotopic
alAlgebra`。
形式化陈述：isFibrant_of_fibration [(fibrations C).IsStableUnderComposition] {X Y : C}
 (p : X ⟶ Y) [Fibration p] [hY : IsFibrant Y] : IsFibrant X
参数：fibrations C；p : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopicalAlgebra.isFibrant_iff`：isFibrant_iff (X : C) : IsFibrant X ↔ 
Fibration (terminal.from X)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `HomotopicalAlgebra.instFibrationCompOfIsStableUnderCompositionFibrations
`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ 
Y) (g : Y ⟶ Z)   [inst_1 : HomotopicalAlgebra.CategoryWithFibr…
-/
lemma isFibrant_of_fibration [(fibrations C).IsStableUnderComposition]
    {X Y : C} (p : X ⟶ Y) [Fibration p] [hY : IsFibrant Y] :
    IsFibrant X := by
  rw [isFibrant_iff] at hY ⊢
  rw [Subsingleton.elim (terminal.from X) (p ≫ terminal.from Y)]
  infer_instance

section

variable (X Y : C) [(fibrations C).IsStableUnderBaseChange]
  [HasBinaryProduct X Y]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hY : IsFibrant Y] :
    Fibration (prod.fst : X ⨯ Y ⟶ X) := by
  rw [isFibrant_iff] at hY
  rw [fibration_iff] at hY ⊢
  exact MorphismProperty.of_isPullback
    (IsPullback.of_isLimit_binaryFan_of_isTerminal
      (limit.isLimit (pair X Y)) terminalIsTerminal).flip hY
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hX : IsFibrant X] : Fibration (prod.snd : X ⨯ Y ⟶ Y) := by
  rw [isFibrant_iff] at hX
  rw [fibration_iff] at hX ⊢
  exact MorphismProperty.of_isPullback
    (IsPullback.of_isLimit_binaryFan_of_isTerminal
      (limit.isLimit (pair X Y)) terminalIsTerminal) hX

end

end

end HomotopicalAlgebra

