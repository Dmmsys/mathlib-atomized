/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Sums.Basic

/-!
# Associator for binary disjoint union of categories.

The associator functor `((C ⊕ D) ⊕ E) ⥤ (C ⊕ (D ⊕ E))` and its inverse form an equivalence.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

open Sum Functor

namespace CategoryTheory.sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  (E : Type u₃) [Category.{v₃} E]

/-- The associator functor `(C ⊕ D) ⊕ E ⥤ C ⊕ (D ⊕ E)` for sums of categories.
-/
/-
**CategoryTheory.sum.associator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.sum`。
形式化陈述：associator : (C oplus D) oplus E ⥤ C oplus (D oplus E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator functor `(C ⊕ D) ⊕ E ⥤ C ⊕ (D ⊕ E)` for sums of categories.
-/
def associator : (C ⊕ D) ⊕ E ⥤ C ⊕ (D ⊕ E) :=
  (inl_ C (D ⊕ E) |>.sum' <| inl_ D E ⋙ inr_ C (D ⊕ E)).sum' <| inr_ D E ⋙ inr_ C (D ⊕ E)

@[simp]
/-
**CategoryTheory.sum.associator_obj_inl_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.sum`。
形式化陈述：associator_obj_inl_inl (X) : (associator C D E).obj (inl (inl X)) = inl X
参数：X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_obj_inl_inl (X) : (associator C D E).obj (inl (inl X)) = inl X :=
  rfl

@[simp]
/-
**CategoryTheory.sum.associator_obj_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.sum`。
形式化陈述：associator_obj_inl_inr (X) : (associator C D E).obj (inl (inr X)) = inr (i
nl X)
参数：X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_obj_inl_inr (X) : (associator C D E).obj (inl (inr X)) = inr (inl X) :=
  rfl

@[simp]
/-
**CategoryTheory.sum.associator_obj_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.sum`。
形式化陈述：associator_obj_inr (X) : (associator C D E).obj (inr X) = inr (inr X)
参数：X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_obj_inr (X) : (associator C D E).obj (inr X) = inr (inr X) :=
  rfl

@[simp]
/-
**CategoryTheory.sum.associator_map_inl_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.sum`。
形式化陈述：associator_map_inl_inl {X Y : C} (f : X ⟶ Y) : (associator C D E).map ((in
l_ _ _).map ((inl_ _ _).map f)) = (inl_ _ _).map f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_map_inl_inl {X Y : C} (f : X ⟶ Y) :
    (associator C D E).map ((inl_ _ _).map ((inl_ _ _).map f)) = (inl_ _ _).map f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.sum.associator_map_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.sum`。
形式化陈述：associator_map_inl_inr {X Y : D} (f : X ⟶ Y) : (associator C D E).map ((in
l_ _ _).map ((inr_ _ _).map f)) = (inr_ _ _).map ((inl_ _ _).map f)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associator_map_inl_inr {X Y : D} (f : X ⟶ Y) :
    (associator C D E).map ((inl_ _ _).map ((inr_ _ _).map f)) =
    (inr_ _ _).map ((inl_ _ _).map f) := by
  simp [associator]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.sum.associator_map_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.sum`。
形式化陈述：associator_map_inr {X Y : E} (f : X ⟶ Y) : (associator C D E).map ((inr_ _
 _).map f) = (inr_ _ _).map ((inr_ _ _).map f)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associator_map_inr {X Y : E} (f : X ⟶ Y) :
    (associator C D E).map ((inr_ _ _).map f) = (inr_ _ _).map ((inr_ _ _).map f) := by
  simp [associator]

/-- Characterizing the composition of the associator and the left inclusion. -/
@[simps!]
/-
**CategoryTheory.sum.inlCompAssociator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.sum`。
形式化陈述：inlCompAssociator : .sum' inl_ D E ⋙ inr_ C (D oplus E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterizing the composition of the associator and the left inclusion.
-/
def inlCompAssociator :
    inl_ (C ⊕ D) E ⋙ associator C D E ≅ inl_ C (D ⊕ E) |>.sum' <| inl_ D E ⋙ inr_ C (D ⊕ E) :=
  (Functor.inlCompSum' _ _)

/-- Characterizing the composition of the associator and the right inclusion. -/
@[simps!]
/-
**CategoryTheory.sum.inrCompAssociator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.sum`。
形式化陈述：inrCompAssociator : inr_ (C oplus D) E ⋙ associator C D E ≅ inr_ D E ⋙ inr
_ C (D oplus E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterizing the composition of the associator and the right inclusion.
-/
def inrCompAssociator : inr_ (C ⊕ D) E ⋙ associator C D E ≅ inr_ D E ⋙ inr_ C (D ⊕ E) :=
  (Functor.inrCompSum' _ _)

/-- Further characterizing the composition of the associator and the left inclusion. -/
@[simps!]
/-
**CategoryTheory.sum.inlCompInlCompAssociator** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.sum`。
形式化陈述：inlCompInlCompAssociator : inl_ C D ⋙ inl_ (C oplus D) E ⋙ associator C D 
E ≅ inl_ C (D oplus E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Further characterizing the composition of the associator and the left inclusion.
-/
def inlCompInlCompAssociator : inl_ C D ⋙ inl_ (C ⊕ D) E ⋙ associator C D E ≅ inl_ C (D ⊕ E) :=
  isoWhiskerLeft (inl_ _ _) (inlCompAssociator C D E) ≪≫ Functor.inlCompSum' _ _

/-- Further characterizing the composition of the associator and the left inclusion. -/
@[simps!]
/-
**CategoryTheory.sum.inrCompInlCompAssociator** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.sum`。
形式化陈述：inrCompInlCompAssociator : inr_ C D ⋙ inl_ (C oplus D) E ⋙ associator C D 
E ≅ inl_ D E ⋙ inr_ C (D oplus E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Further characterizing the composition of the associator and the left inclusion.
-/
def inrCompInlCompAssociator :
    inr_ C D ⋙ inl_ (C ⊕ D) E ⋙ associator C D E ≅ inl_ D E ⋙ inr_ C (D ⊕ E) :=
  isoWhiskerLeft (inr_ _ _) (inlCompAssociator C D E) ≪≫ Functor.inrCompSum' _ _

/-- The inverse associator functor `C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E` for sums of categories.
-/
/-
**CategoryTheory.sum.inverseAssociator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.sum`。
形式化陈述：inverseAssociator : C oplus (D oplus E) ⥤ (C oplus D) oplus E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse associator functor `C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E` for sums of categorie
s.
-/
def inverseAssociator : C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E :=
  inl_ C D ⋙ inl_ (C ⊕ D) E |>.sum' <| (inr_ C D ⋙ inl_ (C ⊕ D) E).sum' <| inr_ (C ⊕ D) E

@[simp]
/-
**CategoryTheory.sum.inverseAssociator_obj_inl** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.sum`。
形式化陈述：inverseAssociator_obj_inl (X) : (inverseAssociator C D E).obj (inl X) = in
l (inl X)
参数：X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inverseAssociator_obj_inl (X) : (inverseAssociator C D E).obj (inl X) = inl (inl X) :=
  rfl

@[simp]
/-
**CategoryTheory.sum.inverseAssociator_obj_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.sum`。
形式化陈述：inverseAssociator_obj_inr_inl (X) : (inverseAssociator C D E).obj (inr (in
l X)) = inl (inr X)
参数：X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inverseAssociator_obj_inr_inl (X) :
    (inverseAssociator C D E).obj (inr (inl X)) = inl (inr X) :=
  rfl

@[simp]
/-
**CategoryTheory.sum.inverseAssociator_obj_inr_inr** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.sum`。
形式化陈述：inverseAssociator_obj_inr_inr (X) : (inverseAssociator C D E).obj (inr (in
r X)) = inr X
参数：X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inverseAssociator_obj_inr_inr (X) : (inverseAssociator C D E).obj (inr (inr X)) = inr X :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.sum.inverseAssociator_map_inl** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.sum`。
形式化陈述：inverseAssociator_map_inl {X Y : C} (f : X ⟶ Y) : (inverseAssociator C D E
).map ((inl_ _ _).map f) = (inl_ _ _).map ((inl_ _ _).map f)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inverseAssociator_map_inl {X Y : C} (f : X ⟶ Y) :
    (inverseAssociator C D E).map ((inl_ _ _).map f) = (inl_ _ _).map ((inl_ _ _).map f) := by
  simp [inverseAssociator]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.sum.inverseAssociator_map_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.sum`。
形式化陈述：inverseAssociator_map_inr_inl {X Y : D} (f : X ⟶ Y) : (inverseAssociator C
 D E).map ((inr_ _ _).map ((inl_ _ _).map f)) = (inl_ _ _).map ((inr_ _ _).map f
)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inverseAssociator_map_inr_inl {X Y : D} (f : X ⟶ Y) :
    (inverseAssociator C D E).map ((inr_ _ _).map ((inl_ _ _).map f)) =
    (inl_ _ _).map ((inr_ _ _).map f) := by
  simp [inverseAssociator]

@[simp]
/-
**CategoryTheory.sum.inverseAssociator_map_inr_inr** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.sum`。
形式化陈述：inverseAssociator_map_inr_inr {X Y : E} (f : X ⟶ Y) : (inverseAssociator C
 D E).map ((inr_ _ _).map ((inr_ _ _).map f)) = (inr_ _ _).map f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inverseAssociator_map_inr_inr {X Y : E} (f : X ⟶ Y) :
    (inverseAssociator C D E).map ((inr_ _ _).map ((inr_ _ _).map f)) =
    (inr_ _ _).map f :=
  rfl

/-- Characterizing the composition of the inverse of the associator and the left inclusion. -/
@[simps!]
/-
**CategoryTheory.sum.inlCompInverseAssociator** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.sum`。
形式化陈述：inlCompInverseAssociator : inl_ C (D oplus E) ⋙ inverseAssociator C D E ≅ 
inl_ C D ⋙ inl_ (C oplus D) E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterizing the composition of the inverse of the associator and the left inc
lusion.
-/
def inlCompInverseAssociator :
    inl_ C (D ⊕ E) ⋙ inverseAssociator C D E ≅ inl_ C D ⋙ inl_ (C ⊕ D) E :=
  Functor.inlCompSum' _ _

/-- Characterizing the composition of the inverse of the associator and the right inclusion. -/
@[simps!]
/-
**CategoryTheory.sum.inrCompInverseAssociator** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.sum`。
形式化陈述：inrCompInverseAssociator : inr_ C (D oplus E) ⋙ inverseAssociator C D E ≅ 
(inr_ C D ⋙ inl_ (C oplus D) E).sum' inr_ (C oplus D) E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterizing the composition of the inverse of the associator and the right in
clusion.
-/
def inrCompInverseAssociator :
    inr_ C (D ⊕ E) ⋙ inverseAssociator C D E ≅ (inr_ C D ⋙ inl_ (C ⊕ D) E).sum' <| inr_ (C ⊕ D) E :=
  Functor.inrCompSum' _ _

/-- Further characterizing the composition of the inverse of the associator and the right
inclusion. -/
@[simps!]
/-
**CategoryTheory.sum.inlCompInrCompInverseAssociator** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.sum`。
形式化陈述：inlCompInrCompInverseAssociator : inl_ D E ⋙ inr_ C (D oplus E) ⋙ inverseA
ssociator C D E ≅ inr_ C D ⋙ inl_ (C oplus D) E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Further characterizing the composition of the inverse of the associator and the 
right
inclusion.
-/
def inlCompInrCompInverseAssociator :
    inl_ D E ⋙ inr_ C (D ⊕ E) ⋙ inverseAssociator C D E ≅ inr_ C D ⋙ inl_ (C ⊕ D) E :=
  isoWhiskerLeft (inl_ _ _) (inrCompInverseAssociator C D E) ≪≫ Functor.inlCompSum' _ _

/-- Further characterizing the composition of the inverse of the associator and the right
inclusion. -/
@[simps!]
/-
**CategoryTheory.sum.inrCompInrCompInverseAssociator** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.sum`。
形式化陈述：inrCompInrCompInverseAssociator : inr_ D E ⋙ inr_ C (D oplus E) ⋙ inverseA
ssociator C D E ≅ inr_ (C oplus D) E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Further characterizing the composition of the inverse of the associator and the 
right
inclusion.
-/
def inrCompInrCompInverseAssociator :
    inr_ D E ⋙ inr_ C (D ⊕ E) ⋙ inverseAssociator C D E ≅ inr_ (C ⊕ D) E :=
  isoWhiskerLeft (inr_ _ _) (inrCompInverseAssociator C D E) ≪≫ Functor.inrCompSum' _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories expressing associativity of sums of categories.
-/
@[simps functor inverse]
/-
**CategoryTheory.sum.associativity** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.sum
`。
形式化陈述：associativity : (C oplus D) oplus E ≌ C oplus (D oplus E) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories expressing associativity of sums of categories.
-/
def associativity : (C ⊕ D) ⊕ E ≌ C ⊕ (D ⊕ E) where
  functor := associator C D E
  inverse := inverseAssociator C D E
  unitIso := Functor.sumIsoExt
    (Functor.sumIsoExt
      ((Functor.associator _ _ _).symm ≪≫ Functor.rightUnitor _ ≪≫
        (isoWhiskerRight (inlCompInlCompAssociator C D E) (inverseAssociator C D E) ≪≫
          inlCompInverseAssociator C D E).symm ≪≫ Functor.associator _ _ _ ≪≫
          isoWhiskerLeft _ (Functor.associator _ _ _))
      ((Functor.associator _ _ _).symm ≪≫ Functor.rightUnitor _ ≪≫
        (isoWhiskerRight (inrCompInlCompAssociator C D E) (inverseAssociator C D E) ≪≫
          Functor.associator _ _ _ ≪≫
          inlCompInrCompInverseAssociator C D E).symm ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _)))
    (Functor.rightUnitor _ ≪≫
      (isoWhiskerRight (inrCompAssociator C D E) (inverseAssociator C D E) ≪≫
        Functor.associator _ _ _ ≪≫ inrCompInrCompInverseAssociator C D E).symm ≪≫
      Functor.associator _ _ _)
  counitIso := Functor.sumIsoExt
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (inlCompInverseAssociator C D E) (associator C D E) ≪≫
      Functor.associator _ _ _ ≪≫ inlCompInlCompAssociator C D E ≪≫ (Functor.rightUnitor _).symm)
    (Functor.sumIsoExt
      ((Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.associator _ _ _ ≪≫
          inlCompInrCompInverseAssociator C D E) (associator C D E) ≪≫
        Functor.associator _ _ _ ≪≫ inrCompInlCompAssociator C D E ≪≫
        (Functor.rightUnitor _).symm ≪≫ Functor.associator _ _ _)
      ((Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.associator _ _ _ ≪≫
          inrCompInrCompInverseAssociator C D E) (associator C D E) ≪≫
        inrCompAssociator C D E ≪≫ isoWhiskerLeft _ (Functor.rightUnitor _).symm))
  functor_unitIso_comp x := match x with
    | inl (inl c) => by simp [inlCompInlCompAssociator, inlCompInverseAssociator]
    | inl (inr d) => by simp [inrCompInlCompAssociator, inlCompInrCompInverseAssociator]
    | inr e => by simp [inrCompAssociator, inrCompInrCompInverseAssociator]
/-
**CategoryTheory.sum.associatorIsEquivalence** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.sum`。
形式化陈述：associatorIsEquivalence : (associator C D E).IsEquivalence
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance associatorIsEquivalence : (associator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).functor.IsEquivalence)
/-
**CategoryTheory.sum.inverseAssociatorIsEquivalence** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.sum`。
形式化陈述：inverseAssociatorIsEquivalence : (inverseAssociator C D E).IsEquivalence
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
instance inverseAssociatorIsEquivalence : (inverseAssociator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).inverse.IsEquivalence)

-- TODO unitors?
-- TODO pentagon natural transformation? ...satisfying?
end CategoryTheory.sum

