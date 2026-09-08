/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

/-!
# The opposite of a triangulated subcategory

In this file, we show that if `P : ObjectProperty C` is a triangulated
subcategory of a pretriangulated category `C`, then `P.op` is a
triangulated subcategory of `Cᵒᵖ`.

-/

public section

namespace CategoryTheory

open Pretriangulated.Opposite Pretriangulated Limits

namespace ObjectProperty

variable {C : Type*} [Category* C]
  [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [P.IsStableUnderShift ℤ] :
    P.op.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := { le_shift _ hX := P.le_shift (-n) _ hX }
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty Cᵒᵖ) [P.IsStableUnderShift ℤ] :
    P.unop.IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift X hX := by
        obtain ⟨m, rfl⟩ : ∃ m, n = -m := ⟨-n , by simp⟩
        exact P.le_shift m _ hX }
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [P.IsTriangulatedClosed₂] : P.op.IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := by
    rw [mem_distTriang_op_iff] at hT
    obtain ⟨X, hX, ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₂' _ hT h₃ h₁
    exact ⟨Opposite.op X, hX, ⟨e.symm.op⟩⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty Cᵒᵖ) [P.IsTriangulatedClosed₂] : P.unop.IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := by
    obtain ⟨X, hX, ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₂' _ (op_distinguished _ hT) h₃ h₁
    exact ⟨Opposite.unop X, hX, ⟨e.symm.unop⟩⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [P.IsTriangulated] : P.op.IsTriangulated where
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty Cᵒᵖ) [P.IsTriangulated] : P.unop.IsTriangulated where
/-
**CategoryTheory.ObjectProperty.trW_of_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ObjectProperty`。
形式化陈述：trW_of_op (P : ObjectProperty C) [P.IsTriangulated] {X Y : C} {f : X ⟶ Y} 
(hf : P.op.trW f.op) : P.trW f
参数：P : ObjectProperty C；hf : P.op.trW f.op。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.instAdditiveOppositeShiftFunctor
Int`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Preadditive…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.trW_iff'`：trW_iff' [P.IsStableUnderShift I
nt] {Y Z : C} (g : Y ⟶ Z) : P.trW g ↔ exists (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 :
 Int)⟧) (_ : Triangle.mk f g…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用引理 `CategoryTheory.Pretriangulated.unop_distinguished`：unop_distinguished (T
 : Triangle Cᵒᵖ) (hT : T in distTriang Cᵒᵖ) : ((triangleOpEquivalence C).inverse
.obj T).unop in distTriang C
-/
lemma trW_of_op (P : ObjectProperty C) [P.IsTriangulated]
    {X Y : C} {f : X ⟶ Y} (hf : P.op.trW f.op) : P.trW f := by
  obtain ⟨Z, a, b, h₁, h₂⟩ := hf
  rw [ObjectProperty.trW_iff']
  exact ⟨_, _, _, Pretriangulated.unop_distinguished _ h₁, h₂⟩
/-
**CategoryTheory.ObjectProperty.trW_of_unop** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：trW_of_unop (P : ObjectProperty Cᵒᵖ) [P.IsTriangulated] {X Y : Cᵒᵖ} {f : X
 ⟶ Y} (hf : P.unop.trW f.unop) : P.trW f
参数：P : ObjectProperty Cᵒᵖ；hf : P.unop.trW f.unop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.instAdditiveOppositeShiftFunctor
Int`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Preadditive…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.trW_iff'`：trW_iff' [P.IsStableUnderShift I
nt] {Y Z : C} (g : Y ⟶ Z) : P.trW g ↔ exists (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 :
 Int)⟧) (_ : Triangle.mk f g…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用引理 `CategoryTheory.Pretriangulated.op_distinguished`：op_distinguished (T : T
riangle C) (hT : T in distTriang C) : ((triangleOpEquivalence C).functor.obj (Op
posite.op T)) in distTriang Cᵒᵖ
-/
lemma trW_of_unop (P : ObjectProperty Cᵒᵖ) [P.IsTriangulated]
    {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : P.unop.trW f.unop) : P.trW f := by
  obtain ⟨Z, a, b, h₁, h₂⟩ := hf
  rw [ObjectProperty.trW_iff']
  exact ⟨_, _, _, Pretriangulated.op_distinguished _ h₁, h₂⟩
/-
**CategoryTheory.ObjectProperty.trW_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ObjectProperty`。
形式化陈述：trW_op_iff (P : ObjectProperty C) [P.IsTriangulated] {X Y : Cᵒᵖ} {f : X ⟶ 
Y} : P.op.trW f ↔ P.trW f.unop
参数：P : ObjectProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.instAdditiveOppositeShiftFunctor
Int`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Preadditive…
· 使用引理 `CategoryTheory.ObjectProperty.trW_of_op`：trW_of_op (P : ObjectProperty C
) [P.IsTriangulated] {X Y : C} {f : X ⟶ Y} (hf : P.op.trW f.op) : P.trW f
· 使用引理 `CategoryTheory.ObjectProperty.trW_of_unop`：trW_of_unop (P : ObjectProper
ty Cᵒᵖ) [P.IsTriangulated] {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : P.unop.trW f.unop) : P.
trW f
· 使用定理 `CategoryTheory.ObjectProperty.instIsTriangulatedOppositeOp`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.HasS
hift C ℤ]   [inst_2 : CategoryTheory.Limits.HasZ…
-/
lemma trW_op_iff (P : ObjectProperty C) [P.IsTriangulated] {X Y : Cᵒᵖ} {f : X ⟶ Y} :
    P.op.trW f ↔ P.trW f.unop :=
  ⟨P.trW_of_op, P.op.trW_of_unop⟩
/-
**CategoryTheory.ObjectProperty.trW_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ObjectProperty`。
形式化陈述：trW_op (P : ObjectProperty C) [P.IsTriangulated] : P.op.trW = P.trW.op
参数：P : ObjectProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.instAdditiveOppositeShiftFunctor
Int`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Preadditive…
· 使用引理 `CategoryTheory.ObjectProperty.trW_op_iff`：trW_op_iff (P : ObjectProperty
 C) [P.IsTriangulated] {X Y : Cᵒᵖ} {f : X ⟶ Y} : P.op.trW f ↔ P.trW f.unop
-/
lemma trW_op (P : ObjectProperty C) [P.IsTriangulated] : P.op.trW = P.trW.op := by
  ext X Y f
  exact P.trW_op_iff

end ObjectProperty

end CategoryTheory

