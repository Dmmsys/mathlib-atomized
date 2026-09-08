/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.Order.Basic

/-! # Properties of objects which are closed under isomorphisms

Given a category `C` and `P : ObjectProperty C` (i.e. `P : C → Prop`),
this file introduces the type class `P.IsClosedUnderIsomorphisms`.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (P Q : ObjectProperty C)

namespace ObjectProperty

/-- A predicate `C → Prop` on the objects of a category is closed under isomorphisms
if whenever `P X`, then all the objects `Y` that are isomorphic to `X` also satisfy `P Y`. -/
/-
**CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms** 是 Mathlib 中的一个归纳类型，位
于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
ObjectProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate `C → Prop` on the objects of a category is closed under isomorphisms
if whenever `P X`, then all the objects `Y` that are isomorphic to `X` also sati
sfy `P Y`.
-/
class IsClosedUnderIsomorphisms : Prop where
  of_iso {X Y : C} (_ : X ≅ Y) (_ : P X) : P Y
/-
**CategoryTheory.ObjectProperty.prop_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：prop_of_iso [IsClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y) (hX : P X)
 : P Y
参数：e : X ≅ Y；hX : P X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms.of_iso`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectPrope
rty C}   [self : P.IsClosedUnderIsomorphisms] {X Y :…
-/
lemma prop_of_iso [IsClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y :=
  IsClosedUnderIsomorphisms.of_iso e hX
/-
**CategoryTheory.ObjectProperty.prop_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：prop_iff_of_iso [IsClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X 
↔ P Y
参数：e : X ≅ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
-/
lemma prop_iff_of_iso [IsClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y :=
  ⟨prop_of_iso P e, prop_of_iso P e.symm⟩
/-
**CategoryTheory.ObjectProperty.prop_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：prop_of_isIso [IsClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f
] (hX : P X) : P Y
参数：f : X ⟶ Y；hX : P X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
-/
lemma prop_of_isIso [IsClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f] (hX : P X) :
    P Y :=
  prop_of_iso P (asIso f) hX
/-
**CategoryTheory.ObjectProperty.prop_iff_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：prop_iff_of_isIso [IsClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsI
so f] : P X ↔ P Y
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_iff_of_iso`：prop_iff_of_iso [IsClosed
UnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y
-/
lemma prop_iff_of_isIso [IsClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f] : P X ↔ P Y :=
  prop_iff_of_iso P (asIso f)

/-- The closure by isomorphisms of a predicate on objects in a category. -/
/-
**CategoryTheory.ObjectProperty.isoClosure** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ObjectProperty`。
形式化陈述：isoClosure : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure by isomorphisms of a predicate on objects in a category.
-/
def isoClosure : ObjectProperty C := fun X => ∃ (Y : C) (_ : P Y), Nonempty (X ≅ Y)
/-
**CategoryTheory.ObjectProperty.prop_isoClosure_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：prop_isoClosure_iff (X : C) : isoClosure P X ↔ exists (Y : C) (_ : P Y), N
onempty (X ≅ Y)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma prop_isoClosure_iff (X : C) :
    isoClosure P X ↔ ∃ (Y : C) (_ : P Y), Nonempty (X ≅ Y) := by rfl

variable {P} in
/-
**CategoryTheory.ObjectProperty.prop_isoClosure** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：prop_isoClosure {X Y : C} (h : P X) (e : X ⟶ Y) [IsIso e] : isoClosure P Y
参数：h : P X；e : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prop_isoClosure {X Y : C} (h : P X) (e : X ⟶ Y) [IsIso e] : isoClosure P Y :=
  ⟨X, h, ⟨(asIso e).symm⟩⟩
/-
**CategoryTheory.ObjectProperty.le_isoClosure** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：le_isoClosure : P <= isoClosure P
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_isoClosure : P ≤ isoClosure P :=
  fun X hX => ⟨X, hX, ⟨Iso.refl X⟩⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.Nonempty] : P.isoClosure.Nonempty := .mono P.le_isoClosure

variable {P Q} in
/-
**CategoryTheory.ObjectProperty.monotone_isoClosure** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：monotone_isoClosure (h : P <= Q) : isoClosure P <= isoClosure Q
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monotone_isoClosure (h : P ≤ Q) : isoClosure P ≤ isoClosure Q := by
  rintro X ⟨X', hX', ⟨e⟩⟩
  exact ⟨X', h _ hX', ⟨e⟩⟩
/-
**CategoryTheory.ObjectProperty.isoClosure_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：isoClosure_eq_self [IsClosedUnderIsomorphisms P] : isoClosure P = P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
-/
lemma isoClosure_eq_self [IsClosedUnderIsomorphisms P] : isoClosure P = P := by
  apply le_antisymm
  · intro X ⟨Y, hY, ⟨e⟩⟩
    exact prop_of_iso P e.symm hY
  · exact le_isoClosure P
/-
**CategoryTheory.ObjectProperty.isoClosure_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：isoClosure_le_iff [IsClosedUnderIsomorphisms Q] : isoClosure P <= Q ↔ P <=
 Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
· 使用引理 `CategoryTheory.ObjectProperty.monotone_isoClosure`：monotone_isoClosure (
h : P <= Q) : isoClosure P <= isoClosure Q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_eq_self`：isoClosure_eq_self [Is
ClosedUnderIsomorphisms P] : isoClosure P = P
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma isoClosure_le_iff [IsClosedUnderIsomorphisms Q] : isoClosure P ≤ Q ↔ P ≤ Q :=
  ⟨(le_isoClosure P).trans,
    fun h => (monotone_isoClosure h).trans (by rw [isoClosure_eq_self])⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsClosedUnderIsomorphisms (isoClosure P) where
  of_iso := by
    rintro X Y e ⟨Z, hZ, ⟨f⟩⟩
    exact ⟨Z, hZ, ⟨e.symm.trans f⟩⟩
/-
**CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_iff_isoClosure_eq_self
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderIsomorphisms_iff_isoClosure_eq_self : IsClosedUnderIsomorphis
ms P ↔ isoClosure P = P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_eq_self`：isoClosure_eq_self [Is
ClosedUnderIsomorphisms P] : isoClosure P = P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsIsoClosure`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Obje
ctProperty C),   P.isoClosure.IsClosedUnderIsomorphisms
-/
lemma isClosedUnderIsomorphisms_iff_isoClosure_eq_self :
    IsClosedUnderIsomorphisms P ↔ isoClosure P = P :=
  ⟨fun _ ↦ isoClosure_eq_self _, fun h ↦ by rw [← h]; infer_instance⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) : IsClosedUnderIsomorphisms (P.map F) where
  of_iso := by
    rintro _ _ e ⟨X, hX, ⟨e'⟩⟩
    exact ⟨X, hX, ⟨e' ≪≫ e⟩⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : D ⥤ C) [P.IsClosedUnderIsomorphisms] :
    IsClosedUnderIsomorphisms (P.inverseImage F) where
  of_iso e hX := P.prop_of_iso (F.mapIso e) hX

@[simp]
/-
**CategoryTheory.ObjectProperty.isoClosure_strictMap** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：isoClosure_strictMap (F : C ⥤ D) : (P.strictMap F).isoClosure = P.map F
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_le_iff`：isoClosure_le_iff [IsCl
osedUnderIsomorphisms Q] : isoClosure P <= Q ↔ P <= Q
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsMap`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : Categor
yTheory.Category.{v', u'} D]   (P : CategoryTheory.O…
· 使用引理 `CategoryTheory.ObjectProperty.strictMap_le_map`：strictMap_le_map (P : Ob
jectProperty C) (F : C ⥤ D) : P.strictMap F <= P.map F
-/
lemma isoClosure_strictMap (F : C ⥤ D) :
    (P.strictMap F).isoClosure = P.map F := by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    exact P.strictMap_le_map F
  · rintro X ⟨Y, hY, ⟨e⟩⟩
    exact ⟨F.obj Y, ⟨Y, hY⟩, ⟨e.symm⟩⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.map_isoClosure** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：map_isoClosure (F : C ⥤ D) : P.isoClosure.map F = P.map F
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.map_monotone`：map_monotone {P Q : ObjectPr
operty C} (h : P <= Q) (F : C ⥤ D) : P.map F <= Q.map F
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
-/
lemma map_isoClosure (F : C ⥤ D) :
    P.isoClosure.map F = P.map F := by
  refine le_antisymm ?_ (map_monotone P.le_isoClosure F)
  rintro X ⟨Y, ⟨Z, hZ, ⟨e⟩⟩, ⟨e'⟩⟩
  exact ⟨Z, hZ, ⟨F.mapIso e.symm ≪≫ e'⟩⟩

end ObjectProperty

end CategoryTheory

