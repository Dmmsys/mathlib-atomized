/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Retract

/-! # Properties of objects which are stable under retracts

Given a category `C` and `P : ObjectProperty C` (i.e. `P : C → Prop`),
this file introduces the type class `P.IsStableUnderRetracts`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- A predicate `C → Prop` on the objects of a category is stable under retracts
if whenever `P Y`, then all the objects `X` that are retracts of `Y` also satisfy `P X`. -/
/-
**CategoryTheory.ObjectProperty.IsStableUnderRetracts** 是 Mathlib 中的一个归纳类型，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
ObjectProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate `C → Prop` on the objects of a category is stable under retracts
if whenever `P Y`, then all the objects `X` that are retracts of `Y` also satisf
y `P X`.
-/
class IsStableUnderRetracts where
  of_retract {X Y : C} (_ : Retract X Y) (_ : P Y) : P X
/-
**CategoryTheory.ObjectProperty.prop_of_retract** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：prop_of_retract [IsStableUnderRetracts P] {X Y : C} (h : Retract X Y) (hY 
: P Y) : P X
参数：h : Retract X Y；hY : P Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_retract`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectPrope
rty C}   [self : P.IsStableUnderRetracts] {X Y : C} …
-/
lemma prop_of_retract [IsStableUnderRetracts P] {X Y : C} (h : Retract X Y) (hY : P Y) : P X :=
  IsStableUnderRetracts.of_retract h hY
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderRetracts (⊥ : ObjectProperty C) where
  of_retract _ h := h
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderRetracts (⊤ : ObjectProperty C) where
  of_retract _ _ := by trivial

namespace IsStableUnderRetracts

open scoped ZeroObject

variable [P.IsStableUnderRetracts]

/-
**CategoryTheory.ObjectProperty.IsStableUnderRetracts.** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.ObjectProperty.IsStableUnderRetracts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.IsClosedUnderIsomorphisms where
  of_iso i h := IsStableUnderRetracts.of_retract i.symm.retract h

-- see Note [lower instance priority]
/-
**CategoryTheory.ObjectProperty.IsStableUnderRetracts.** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.ObjectProperty.IsStableUnderRetracts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [HasZeroObject C] [P.Nonempty] : P.ContainsZero where
  exists_zero := ⟨0, isZero_zero _, of_retract ((isZero_zero _).retract _) P.prop_arbitrary⟩

@[deprecated instContainsZeroOfHasZeroObjectOfNonempty (since := "2026-04-03")]
/-
**CategoryTheory.ObjectProperty.IsStableUnderRetracts.containsZero** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsStableUnderRetracts`。
形式化陈述：containsZero [HasZeroObject C] {X : C} (h : P X) : P.ContainsZero where ex
ists_zero
参数：h : P X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
· 使用定理 `CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_retract`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectPrope
rty C}   [self : P.IsStableUnderRetracts] {X Y : C} …
-/
lemma containsZero [HasZeroObject C] {X : C} (h : P X) : P.ContainsZero where
  exists_zero := ⟨0, isZero_zero _, of_retract ((isZero_zero _).retract X) h⟩
/-
**CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_binaryBicone_left** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsStableUnderRetracts`。
形式化陈述：of_binaryBicone_left [HasZeroMorphisms C] {X Y : C} (c : BinaryBicone X Y)
 (h : P c.pt) : P X
参数：c : BinaryBicone X Y；h : P c.pt。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_retract`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectPrope
rty C}   [self : P.IsStableUnderRetracts] {X Y : C} …
-/
lemma of_binaryBicone_left [HasZeroMorphisms C] {X Y : C} (c : BinaryBicone X Y) (h : P c.pt) :
    P X :=
  of_retract c.retract_left h
/-
**CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_binaryBicone_right** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsStableUnderRetracts`。
形式化陈述：of_binaryBicone_right [HasZeroMorphisms C] {X Y : C} (c : BinaryBicone X Y
) (h : P c.pt) : P Y
参数：c : BinaryBicone X Y；h : P c.pt。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_retract`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectPrope
rty C}   [self : P.IsStableUnderRetracts] {X Y : C} …
-/
lemma of_binaryBicone_right [HasZeroMorphisms C] {X Y : C} (c : BinaryBicone X Y) (h : P c.pt) :
    P Y :=
  of_retract c.retract_right h
/-
**CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_biprod_left** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsStableUnderRetracts`。
形式化陈述：of_biprod_left [HasZeroMorphisms C] {X Y : C} [HasBinaryBiproduct X Y] (h 
: P (X ⊞ Y)) : P X
参数：h : P (X ⊞ Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_binaryBicone_left
`：of_binaryBicone_left [HasZeroMorphisms C] {X Y : C} (c : BinaryBicone X Y) (h 
: P c.pt) : P X
-/
lemma of_biprod_left [HasZeroMorphisms C] {X Y : C} [HasBinaryBiproduct X Y] (h : P (X ⊞ Y)) :
    P X :=
  of_binaryBicone_left P (BinaryBiproduct.bicone X Y) h
/-
**CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_biprod_right** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsStableUnderRetracts`。
形式化陈述：of_biprod_right [HasZeroMorphisms C] {X Y : C} [HasBinaryBiproduct X Y] (h
 : P (X ⊞ Y)) : P Y
参数：h : P (X ⊞ Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_binaryBicone_righ
t`：of_binaryBicone_right [HasZeroMorphisms C] {X Y : C} (c : BinaryBicone X Y) (
h : P c.pt) : P Y
-/
lemma of_biprod_right [HasZeroMorphisms C] {X Y : C} [HasBinaryBiproduct X Y] (h : P (X ⊞ Y)) :
    P Y :=
  of_binaryBicone_right P (BinaryBiproduct.bicone X Y) h
/-
**CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_bicone** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ObjectProperty.IsStableUnderRetracts`。
形式化陈述：of_bicone [HasZeroMorphisms C] {J : Type*} (F : J -> C) (c : Bicone F) (h 
: P c.pt) (j : J) : P (F j)
参数：F : J -> C；c : Bicone F；h : P c.pt；j : J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_retract`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectPrope
rty C}   [self : P.IsStableUnderRetracts] {X Y : C} …
-/
lemma of_bicone [HasZeroMorphisms C] {J : Type*} (F : J → C) (c : Bicone F) (h : P c.pt) (j : J) :
    P (F j) :=
  of_retract (c.retract j) h
/-
**CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_biproduct** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsStableUnderRetracts`。
形式化陈述：of_biproduct [HasZeroMorphisms C] {J : Type*} (F : J -> C) [HasBiproduct F
] (h : P (⨁ F)) (j : J) : P (F j)
参数：F : J -> C；h : P (⨁ F)；j : J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.IsStableUnderRetracts.of_bicone`：of_bicone
 [HasZeroMorphisms C] {J : Type*} (F : J -> C) (c : Bicone F) (h : P c.pt) (j : 
J) : P (F j)
-/
lemma of_biproduct [HasZeroMorphisms C] {J : Type*} (F : J → C) [HasBiproduct F] (h : P (⨁ F))
    (j : J) : P (F j) :=
  of_bicone P F (biproduct.bicone F) h j

end IsStableUnderRetracts

/-- The closure by retracts of a predicate on objects in a category. -/
/-
**CategoryTheory.ObjectProperty.retractClosure** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：retractClosure : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure by retracts of a predicate on objects in a category.
-/
def retractClosure : ObjectProperty C := fun X => ∃ (Y : C) (_ : P Y), Nonempty (Retract X Y)
/-
**CategoryTheory.ObjectProperty.prop_retractClosure_iff** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：prop_retractClosure_iff (X : C) : retractClosure P X ↔ exists (Y : C) (_ :
 P Y), Nonempty (Retract X Y)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma prop_retractClosure_iff (X : C) :
    retractClosure P X ↔ ∃ (Y : C) (_ : P Y), Nonempty (Retract X Y) := by rfl

variable {P} in
/-
**CategoryTheory.ObjectProperty.prop_retractClosure** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：prop_retractClosure {X Y : C} (h : P Y) (r : Retract X Y) : retractClosure
 P X
参数：h : P Y；r : Retract X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prop_retractClosure {X Y : C} (h : P Y) (r : Retract X Y) : retractClosure P X :=
  ⟨Y, h, ⟨r⟩⟩
/-
**CategoryTheory.ObjectProperty.le_retractClosure** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：le_retractClosure : P <= retractClosure P
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_retractClosure : P ≤ retractClosure P :=
  fun X hX => ⟨X, hX, ⟨Retract.refl X⟩⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.Nonempty] : P.retractClosure.Nonempty :=
  .mono P.le_retractClosure

variable {P Q} in
/-
**CategoryTheory.ObjectProperty.monotone_retractClosure** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：monotone_retractClosure (h : P <= Q) : retractClosure P <= retractClosure 
Q
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monotone_retractClosure (h : P ≤ Q) : retractClosure P ≤ retractClosure Q := by
  rintro X ⟨X', hX', ⟨e⟩⟩
  exact ⟨X', h _ hX', ⟨e⟩⟩
/-
**CategoryTheory.ObjectProperty.retractClosure_eq_self** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：retractClosure_eq_self [IsStableUnderRetracts P] : retractClosure P = P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_retract`：prop_of_retract [IsStable
UnderRetracts P] {X Y : C} (h : Retract X Y) (hY : P Y) : P X
· 使用引理 `CategoryTheory.ObjectProperty.le_retractClosure`：le_retractClosure : P <
= retractClosure P
-/
lemma retractClosure_eq_self [IsStableUnderRetracts P] : retractClosure P = P := by
  apply le_antisymm
  · intro X ⟨Y, hY, ⟨e⟩⟩
    exact prop_of_retract P e hY
  · exact le_retractClosure P

@[simp]
/-
**CategoryTheory.ObjectProperty.retractClosure_bot** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：retractClosure_bot : retractClosure (⊥ : ObjectProperty C) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_eq_self`：retractClosure_eq_
self [IsStableUnderRetracts P] : retractClosure P = P
· 使用定理 `CategoryTheory.ObjectProperty.instIsStableUnderRetractsBot`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C], ⊥.IsStableUnderRetracts
-/
lemma retractClosure_bot : retractClosure (⊥ : ObjectProperty C) = ⊥ :=
  retractClosure_eq_self _

@[simp]
/-
**CategoryTheory.ObjectProperty.retractClosure_top** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：retractClosure_top : retractClosure (⊤ : ObjectProperty C) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_eq_self`：retractClosure_eq_
self [IsStableUnderRetracts P] : retractClosure P = P
· 使用定理 `CategoryTheory.ObjectProperty.instIsStableUnderRetractsTop`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderRetracts
-/
lemma retractClosure_top : retractClosure (⊤ : ObjectProperty C) = ⊤ :=
  retractClosure_eq_self _
/-
**CategoryTheory.ObjectProperty.retractClosure_le_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：retractClosure_le_iff (Q : ObjectProperty C) [IsStableUnderRetracts Q] : r
etractClosure P <= Q ↔ P <= Q
参数：Q : ObjectProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.ObjectProperty.le_retractClosure`：le_retractClosure : P <
= retractClosure P
· 使用引理 `CategoryTheory.ObjectProperty.monotone_retractClosure`：monotone_retractC
losure (h : P <= Q) : retractClosure P <= retractClosure Q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_eq_self`：retractClosure_eq_
self [IsStableUnderRetracts P] : retractClosure P = P
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma retractClosure_le_iff (Q : ObjectProperty C) [IsStableUnderRetracts Q] :
    retractClosure P ≤ Q ↔ P ≤ Q :=
  ⟨(le_retractClosure P).trans,
    fun h => (monotone_retractClosure h).trans (by rw [retractClosure_eq_self])⟩
/-
**CategoryTheory.ObjectProperty.retractClosure_isoClosure** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：retractClosure_isoClosure : P.isoClosure.retractClosure = P.retractClosure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.monotone_retractClosure`：monotone_retractC
losure (h : P <= Q) : retractClosure P <= retractClosure Q
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
-/
lemma retractClosure_isoClosure :
    P.isoClosure.retractClosure = P.retractClosure := by
  refine le_antisymm ?_ (monotone_retractClosure P.le_isoClosure)
  rintro Y ⟨X, ⟨X', hX', ⟨e⟩⟩, ⟨h⟩⟩
  exact ⟨_, hX', ⟨h.trans (Retract.ofIso e)⟩⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderRetracts (retractClosure P) where
  of_retract := by
    rintro X Y r₁ ⟨Z, hZ, ⟨r₂⟩⟩
    refine ⟨Z, hZ, ⟨r₁.trans r₂⟩⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.retractClosure_retractClosure** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：retractClosure_retractClosure : P.retractClosure.retractClosure = P.retrac
tClosure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_eq_self`：retractClosure_eq_
self [IsStableUnderRetracts P] : retractClosure P = P
· 使用定理 `CategoryTheory.ObjectProperty.instIsStableUnderRetractsRetractClosure`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Obje
ctProperty C),   P.retractClosure.IsStableUnderRetracts
-/
lemma retractClosure_retractClosure :
    P.retractClosure.retractClosure = P.retractClosure :=
  retractClosure_eq_self P.retractClosure
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} P.retractClosure where
  exists_small_le' := by
    obtain ⟨Q, _, h₁, h₂⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{w} P
    let α := Σ (X : Subtype Q), { p : X.1 ⟶ X.1 // p ≫ p = p }
    let g {X Y : C} (h : Retract Y X) (hX : Q X) : α := ⟨⟨X, hX⟩, h.r ≫ h.i, by simp⟩
    let R (a : α) : Prop := ∃ (X Y : C) (h : Retract Y X) (hX : Q X), g h hX = a
    choose X Y h hX using fun (a : Subtype R) ↦ a.2
    refine ⟨.ofObj Y, inferInstance, (monotone_retractClosure h₂).trans ?_⟩
    rw [retractClosure_isoClosure]
    rintro y ⟨x, hx, ⟨r⟩⟩
    obtain ⟨a, h₁, h₂⟩ : ∃ (a : Subtype R) (h₁ : Q (X a)), g (h a) h₁ = g r hx := by
      obtain ⟨_, hr⟩ := hX ⟨⟨⟨_, hx⟩, r.r ≫ r.i, by simp⟩, ⟨_, _, r, hx, rfl⟩⟩
      exact ⟨_, _, hr⟩
    obtain rfl : x = X a := Subtype.ext_iff.1 (congr_arg Sigma.fst h₂.symm)
    have hri : (h a).r ≫ (h a).i = r.r ≫ r.i := by
      rw [Sigma.ext_iff, heq_eq_eq] at h₂
      exact Subtype.ext_iff.1 h₂.2
    exact ⟨_, ⟨a.1, a.2⟩, ⟨{
      hom := r.i ≫ (h a).r
      inv := (h a).i ≫ r.r
      hom_inv_id := by simp [reassoc_of% hri]
      inv_hom_id := by simp [← reassoc_of% hri]
    }⟩⟩

end CategoryTheory.ObjectProperty

