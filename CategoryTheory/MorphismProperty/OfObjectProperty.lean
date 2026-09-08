/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Morphism properties from object properties

Given two object properties `P` and `Q`, we introduce a morphism property
`ofObjectProperty P Q`, given by all morphisms whose source satisfies `P` and
target satisfies `Q`.

-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category* C]

/-- Given two object properties `P` and `Q`, the property of morphisms whose source
satisfies `P` and target satisfies `Q`. -/
/-
**CategoryTheory.MorphismProperty.ofObjectProperty** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：ofObjectProperty (P Q : ObjectProperty C) : MorphismProperty C
参数：P Q : ObjectProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two object properties `P` and `Q`, the property of morphisms whose source
satisfies `P` and target satisfies `Q`.
-/
def ofObjectProperty (P Q : ObjectProperty C) : MorphismProperty C := fun X Y _ => P X ∧ Q Y

variable (P Q : ObjectProperty C)
/-
**CategoryTheory.MorphismProperty.ofObjectProperty_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：ofObjectProperty_iff {X Y : C} (f : X ⟶ Y) : ofObjectProperty P Q f ↔ P X 
∧ Q Y
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofObjectProperty_iff {X Y : C} (f : X ⟶ Y) :
    ofObjectProperty P Q f ↔ P X ∧ Q Y := Iff.rfl

variable {P} in
/-
**CategoryTheory.MorphismProperty.monotone_ofObjectProperty_left** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：monotone_ofObjectProperty_left {P' : ObjectProperty C} (h : P <= P') : ofO
bjectProperty P Q <= ofObjectProperty P' Q
参数：h : P <= P'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monotone_ofObjectProperty_left {P' : ObjectProperty C} (h : P ≤ P') :
    ofObjectProperty P Q ≤ ofObjectProperty P' Q := by
  intro _ _ _ ⟨hX, hY⟩
  exact ⟨h _ hX, hY⟩

variable {Q} in
/-
**CategoryTheory.MorphismProperty.monotone_ofObjectProperty_right** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：monotone_ofObjectProperty_right {Q' : ObjectProperty C} (h : Q <= Q') : of
ObjectProperty P Q <= ofObjectProperty P Q'
参数：h : Q <= Q'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monotone_ofObjectProperty_right {Q' : ObjectProperty C} (h : Q ≤ Q') :
    ofObjectProperty P Q ≤ ofObjectProperty P Q' := by
  intro _ _ _ ⟨hX, hY⟩
  exact ⟨hX, h _ hY⟩
/-
**CategoryTheory.MorphismProperty.ofObjectProperty_inverseImage** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：ofObjectProperty_inverseImage {D : Type*} [Category* D] (F : D ⥤ C) : ofOb
jectProperty (P.inverseImage F) (Q.inverseImage F) = (ofObjectProperty P Q).inve
rseImage F
参数：F : D ⥤ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofObjectProperty_inverseImage {D : Type*} [Category* D] (F : D ⥤ C) :
    ofObjectProperty (P.inverseImage F) (Q.inverseImage F) =
    (ofObjectProperty P Q).inverseImage F := by
  rfl
/-
**CategoryTheory.MorphismProperty.ofObjectProperty_map_le** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：ofObjectProperty_map_le {D : Type*} [Category* D] (F : C ⥤ D) : (ofObjectP
roperty P Q).map F <= ofObjectProperty (P.map F) (Q.map F)
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofObjectProperty_map_le {D : Type*} [Category* D] (F : C ⥤ D) :
    (ofObjectProperty P Q).map F ≤ ofObjectProperty (P.map F) (Q.map F) := by
  intro X Y f ⟨X', Y', f', ⟨hX', hY'⟩, ⟨i⟩⟩
  exact ⟨⟨X', hX', ⟨Comma.leftIso i⟩⟩, ⟨Y', hY', ⟨Comma.rightIso i⟩⟩⟩
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderIsomorphisms] : (ofObjectProperty P Q).RespectsLeft (isomorphisms C) where
  precomp := by
    intro X Y Z i hi f ⟨hY, hZ⟩
    rw [isomorphisms.iff] at hi
    exact ⟨(P.prop_iff_of_isIso i).mpr hY, hZ⟩
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Q.IsClosedUnderIsomorphisms] : (ofObjectProperty P Q).RespectsRight (isomorphisms C) where
  postcomp := by
    intro X Y Z i hi f ⟨hY, hZ⟩
    rw [isomorphisms.iff] at hi
    exact ⟨hY, (Q.prop_iff_of_isIso i).mp hZ⟩

end CategoryTheory.MorphismProperty

