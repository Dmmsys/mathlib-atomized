/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.Opposites

/-!
# The opposite of a property of objects

-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Opposite

variable {C : Type u}

section

variable [CategoryStruct.{v} C]

/-- The property of objects of `Cᵒᵖ` corresponding to `P : ObjectProperty C`. -/
/-
**CategoryTheory.ObjectProperty.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Obj
ectProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.CategoryStruct.{v, u} C] → Categor
yTheory.ObjectProperty C → CategoryTheory.ObjectProperty Cᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects of `Cᵒᵖ` corresponding to `P : ObjectProperty C`.
-/
protected def op (P : ObjectProperty C) : ObjectProperty Cᵒᵖ :=
  fun X ↦ P X.unop

/-- The property of objects of `C` corresponding to `P : ObjectProperty Cᵒᵖ`. -/
/-
**CategoryTheory.ObjectProperty.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.O
bjectProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.CategoryStruct.{v, u} C] → Categor
yTheory.ObjectProperty Cᵒᵖ → CategoryTheory.ObjectProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects of `C` corresponding to `P : ObjectProperty Cᵒᵖ`.
-/
protected def unop (P : ObjectProperty Cᵒᵖ) : ObjectProperty C :=
  fun X ↦ P (op X)

@[simp]
/-
**CategoryTheory.ObjectProperty.op_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ObjectProperty`。
形式化陈述：op_iff (P : ObjectProperty C) (X : Cᵒᵖ) : P.op X ↔ P X.unop
参数：P : ObjectProperty C；X : Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma op_iff (P : ObjectProperty C) (X : Cᵒᵖ) :
    P.op X ↔ P X.unop := Iff.rfl

@[simp]
/-
**CategoryTheory.ObjectProperty.unop_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ObjectProperty`。
形式化陈述：unop_iff (P : ObjectProperty Cᵒᵖ) (X : C) : P.unop X ↔ P (op X)
参数：P : ObjectProperty Cᵒᵖ；X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma unop_iff (P : ObjectProperty Cᵒᵖ) (X : C) :
    P.unop X ↔ P (op X) := Iff.rfl
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [P.Nonempty] : P.op.Nonempty :=
  ⟨op P.arbitrary, P.prop_arbitrary⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty Cᵒᵖ) [P.Nonempty] : P.unop.Nonempty :=
  ⟨P.arbitrary.unop, P.prop_arbitrary⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.op_unop** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ObjectProperty`。
形式化陈述：op_unop (P : ObjectProperty Cᵒᵖ) : P.unop.op = P
参数：P : ObjectProperty Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_unop (P : ObjectProperty Cᵒᵖ) : P.unop.op = P := rfl

@[simp]
/-
**CategoryTheory.ObjectProperty.unop_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ObjectProperty`。
形式化陈述：unop_op (P : ObjectProperty C) : P.op.unop = P
参数：P : ObjectProperty C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unop_op (P : ObjectProperty C) : P.op.unop = P := rfl
/-
**CategoryTheory.ObjectProperty.op_injective** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：op_injective {P Q : ObjectProperty C} (h : P.op = Q.op) : P = Q
参数：h : P.op = Q.op。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.unop_op`：unop_op (P : ObjectProperty C) : 
P.op.unop = P
-/
lemma op_injective {P Q : ObjectProperty C} (h : P.op = Q.op) : P = Q := by
  rw [← P.unop_op, ← Q.unop_op, h]
/-
**CategoryTheory.ObjectProperty.unop_injective** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：unop_injective {P Q : ObjectProperty Cᵒᵖ} (h : P.unop = Q.unop) : P = Q
参数：h : P.unop = Q.unop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.op_unop`：op_unop (P : ObjectProperty Cᵒᵖ) 
: P.unop.op = P
-/
lemma unop_injective {P Q : ObjectProperty Cᵒᵖ} (h : P.unop = Q.unop) : P = Q := by
  rw [← P.op_unop, ← Q.op_unop, h]
/-
**CategoryTheory.ObjectProperty.op_injective_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：op_injective_iff {P Q : ObjectProperty C} : P.op = Q.op ↔ P = Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.op_injective`：op_injective {P Q : ObjectPr
operty C} (h : P.op = Q.op) : P = Q
-/
lemma op_injective_iff {P Q : ObjectProperty C} :
    P.op = Q.op ↔ P = Q :=
  ⟨op_injective, by rintro rfl; rfl⟩
/-
**CategoryTheory.ObjectProperty.unop_injective_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：unop_injective_iff {P Q : ObjectProperty Cᵒᵖ} : P.unop = Q.unop ↔ P = Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.unop_injective`：unop_injective {P Q : Obje
ctProperty Cᵒᵖ} (h : P.unop = Q.unop) : P = Q
-/
lemma unop_injective_iff {P Q : ObjectProperty Cᵒᵖ} :
    P.unop = Q.unop ↔ P = Q :=
  ⟨unop_injective, by rintro rfl; rfl⟩
/-
**CategoryTheory.ObjectProperty.op_monotone** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：op_monotone {P Q : ObjectProperty C} (h : P <= Q) : P.op <= Q.op
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_monotone {P Q : ObjectProperty C} (h : P ≤ Q) : P.op ≤ Q.op :=
  fun _ hX ↦ h _ hX
/-
**CategoryTheory.ObjectProperty.unop_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：unop_monotone {P Q : ObjectProperty Cᵒᵖ} (h : P <= Q) : P.unop <= Q.unop
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unop_monotone {P Q : ObjectProperty Cᵒᵖ} (h : P ≤ Q) : P.unop ≤ Q.unop :=
  fun _ hX ↦ h _ hX

@[simp]
/-
**CategoryTheory.ObjectProperty.op_monotone_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：op_monotone_iff {P Q : ObjectProperty C} : P.op <= Q.op ↔ P <= Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.unop_monotone`：unop_monotone {P Q : Object
Property Cᵒᵖ} (h : P <= Q) : P.unop <= Q.unop
· 使用引理 `CategoryTheory.ObjectProperty.op_monotone`：op_monotone {P Q : ObjectProp
erty C} (h : P <= Q) : P.op <= Q.op
-/
lemma op_monotone_iff {P Q : ObjectProperty C} : P.op ≤ Q.op ↔ P ≤ Q :=
  ⟨unop_monotone, op_monotone⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.unop_monotone_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：unop_monotone_iff {P Q : ObjectProperty Cᵒᵖ} : P.unop <= Q.unop ↔ P <= Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.op_monotone`：op_monotone {P Q : ObjectProp
erty C} (h : P <= Q) : P.op <= Q.op
· 使用引理 `CategoryTheory.ObjectProperty.unop_monotone`：unop_monotone {P Q : Object
Property Cᵒᵖ} (h : P <= Q) : P.unop <= Q.unop
-/
lemma unop_monotone_iff {P Q : ObjectProperty Cᵒᵖ} : P.unop ≤ Q.unop ↔ P ≤ Q :=
  ⟨op_monotone, unop_monotone⟩

/-- The bijection `Subtype P.op ≃ Subtype P` for `P : ObjectProperty C`. -/
/-
**CategoryTheory.ObjectProperty.subtypeOpEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：subtypeOpEquiv (P : ObjectProperty C) : Subtype P.op ≃ Subtype P where toF
un x
参数：P : ObjectProperty C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The bijection `Subtype P.op ≃ Subtype P` for `P : ObjectProperty C`.
-/
def subtypeOpEquiv (P : ObjectProperty C) :
    Subtype P.op ≃ Subtype P where
  toFun x := ⟨x.1.unop, x.2⟩
  invFun x := ⟨op x.1, x.2⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.op_ofObj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ObjectProperty`。
形式化陈述：op_ofObj {ι : Type*} (X : ι -> C) : (ofObj X).op = ofObj (fun i => op (X i
))
参数：X : ι -> C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma op_ofObj {ι : Type*} (X : ι → C) : (ofObj X).op = ofObj (fun i ↦ op (X i)) := by
  ext Z
  simp only [op_iff, ofObj_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [hi]⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← hi]⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.unop_ofObj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ObjectProperty`。
形式化陈述：unop_ofObj {ι : Type*} (X : ι -> Cᵒᵖ) : (ofObj X).unop = ofObj (fun i => (
X i).unop)
参数：X : ι -> Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.op_injective`：op_injective {P Q : ObjectPr
operty C} (h : P.op = Q.op) : P = Q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.op_ofObj`：op_ofObj {ι : Type*} (X : ι -> C
) : (ofObj X).op = ofObj (fun i => op (X i))
-/
lemma unop_ofObj {ι : Type*} (X : ι → Cᵒᵖ) : (ofObj X).unop = ofObj (fun i ↦ (X i).unop) :=
  op_injective ((op_ofObj _).symm)

@[simp high]
/-
**CategoryTheory.ObjectProperty.op_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：op_singleton (X : C) : (singleton X).op = singleton (op X)
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.op_ofObj`：op_ofObj {ι : Type*} (X : ι -> C
) : (ofObj X).op = ofObj (fun i => op (X i))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma op_singleton (X : C) :
    (singleton X).op = singleton (op X) := by
  simp

@[simp high]
/-
**CategoryTheory.ObjectProperty.unop_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：unop_singleton (X : Cᵒᵖ) : (singleton X).unop = singleton X.unop
参数：X : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.unop_ofObj`：unop_ofObj {ι : Type*} (X : ι 
-> Cᵒᵖ) : (ofObj X).unop = ofObj (fun i => (X i).unop)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unop_singleton (X : Cᵒᵖ) :
    (singleton X).unop = singleton X.unop := by
  simp

end

section

variable [Category.{v} C]

/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    P.op.IsClosedUnderIsomorphisms where
  of_iso e hX := P.prop_of_iso e.symm.unop hX
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty Cᵒᵖ) [P.IsClosedUnderIsomorphisms] :
    P.unop.IsClosedUnderIsomorphisms where
  of_iso e hX := P.prop_of_iso e.symm.op hX
/-
**CategoryTheory.ObjectProperty.op_isoClosure** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：op_isoClosure (P : ObjectProperty C) : P.isoClosure.op = P.op.isoClosure
参数：P : ObjectProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma op_isoClosure (P : ObjectProperty C) :
    P.isoClosure.op = P.op.isoClosure := by
  ext ⟨X⟩
  exact ⟨fun ⟨Y, h, ⟨e⟩⟩ ↦ ⟨op Y, h, ⟨e.op.symm⟩⟩,
    fun ⟨Y, h, ⟨e⟩⟩ ↦ ⟨Y.unop, h, ⟨e.unop.symm⟩⟩⟩
/-
**CategoryTheory.ObjectProperty.unop_isoClosure** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：unop_isoClosure (P : ObjectProperty Cᵒᵖ) : P.isoClosure.unop = P.unop.isoC
losure
参数：P : ObjectProperty Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.op_injective_iff`：op_injective_iff {P Q : 
ObjectProperty C} : P.op = Q.op ↔ P = Q
· 使用引理 `CategoryTheory.ObjectProperty.op_isoClosure`：op_isoClosure (P : ObjectPr
operty C) : P.isoClosure.op = P.op.isoClosure
· 使用引理 `CategoryTheory.ObjectProperty.op_unop`：op_unop (P : ObjectProperty Cᵒᵖ) 
: P.unop.op = P
-/
lemma unop_isoClosure (P : ObjectProperty Cᵒᵖ) :
    P.isoClosure.unop = P.unop.isoClosure := by
  rw [← op_injective_iff, P.unop.op_isoClosure, op_unop, op_unop]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given `P : ObjectProperty C`, this is the equivalence between `P.op.FullSubcategory`
and `P.FullSubcategoryᵒᵖ`. -/
@[simps]
/-
**CategoryTheory.ObjectProperty.opEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：opEquivalence (P : ObjectProperty C) : P.op.FullSubcategory ≌ P.FullSubcat
egoryᵒᵖ where functor
参数：P : ObjectProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ObjectProperty C`, this is the equivalence between `P.op.FullSubcateg
ory`
and `P.FullSubcategoryᵒᵖ`.
-/
def opEquivalence (P : ObjectProperty C) : P.op.FullSubcategory ≌ P.FullSubcategoryᵒᵖ where
  functor := (P.lift P.op.ι.leftOp (fun X ↦ X.unop.property)).rightOp
  inverse := P.op.lift P.ι.op (fun X ↦ X.unop.property)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := Quiver.Hom.unop_inj (by cat_disch)

@[simp]
/-
**CategoryTheory.ObjectProperty.op_inf** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ObjectProperty`。
形式化陈述：op_inf (P Q : ObjectProperty C) : (P ⊓ Q).op = P.op ⊓ Q.op
参数：P Q : ObjectProperty C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_inf (P Q : ObjectProperty C) : (P ⊓ Q).op = P.op ⊓ Q.op := rfl

@[simp]
/-
**CategoryTheory.ObjectProperty.op_sup** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ObjectProperty`。
形式化陈述：op_sup (P Q : ObjectProperty C) : (P ⊔ Q).op = P.op ⊔ Q.op
参数：P Q : ObjectProperty C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_sup (P Q : ObjectProperty C) : (P ⊔ Q).op = P.op ⊔ Q.op := rfl

@[simp]
/-
**CategoryTheory.ObjectProperty.unop_inf** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ObjectProperty`。
形式化陈述：unop_inf (P Q : ObjectProperty Cᵒᵖ) : (P ⊓ Q).unop = P.unop ⊓ Q.unop
参数：P Q : ObjectProperty Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unop_inf (P Q : ObjectProperty Cᵒᵖ) : (P ⊓ Q).unop = P.unop ⊓ Q.unop := rfl

@[simp]
/-
**CategoryTheory.ObjectProperty.unop_sup** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ObjectProperty`。
形式化陈述：unop_sup (P Q : ObjectProperty Cᵒᵖ) : (P ⊔ Q).unop = P.unop ⊔ Q.unop
参数：P Q : ObjectProperty Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unop_sup (P Q : ObjectProperty Cᵒᵖ) : (P ⊔ Q).unop = P.unop ⊔ Q.unop := rfl

end

end CategoryTheory.ObjectProperty

