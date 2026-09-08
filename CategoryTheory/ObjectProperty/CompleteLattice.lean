/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Order.CompleteLattice.Basic

/-!
# ObjectProperty is a complete lattice

-/

public section

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : CompleteLattice (ObjectProperty C) := inferInstance

section

variable (P Q : ObjectProperty C) (X : C)

/-
**CategoryTheory.ObjectProperty.prop_inf_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P Q : CategoryTh
eory.ObjectProperty C) (X : C),   (P ⊓ Q) X ↔ P X ∧ Q X
参数：P Q : CategoryTheory.ObjectProperty C；X : C；P ⊓ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp high] lemma prop_inf_iff : (P ⊓ Q) X ↔ P X ∧ Q X := Iff.rfl
/-
**CategoryTheory.ObjectProperty.prop_sup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P Q : CategoryTh
eory.ObjectProperty C) (X : C),   (P ⊔ Q) X ↔ P X ∨ Q X
参数：P Q : CategoryTheory.ObjectProperty C；X : C；P ⊔ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp high] lemma prop_sup_iff : (P ⊔ Q) X ↔ P X ∨ Q X := Iff.rfl
/-
**CategoryTheory.ObjectProperty.nonempty_sup_left** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：nonempty_sup_left [P.Nonempty] : (P ⊔ Q).Nonempty
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.nonempty_of_prop`：nonempty_of_prop {P : Ob
jectProperty C} {X : C} (h : P X) : P.Nonempty
· 使用引理 `CategoryTheory.ObjectProperty.prop_arbitrary`：prop_arbitrary (P : Object
Property C) [P.Nonempty] : P P.arbitrary
-/
instance nonempty_sup_left [P.Nonempty] : (P ⊔ Q).Nonempty :=
  nonempty_of_prop (Or.inl P.prop_arbitrary)
/-
**CategoryTheory.ObjectProperty.nonempty_sup_right** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：nonempty_sup_right [Q.Nonempty] : (P ⊔ Q).Nonempty
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.nonempty_of_prop`：nonempty_of_prop {P : Ob
jectProperty C} {X : C} (h : P X) : P.Nonempty
· 使用引理 `CategoryTheory.ObjectProperty.prop_arbitrary`：prop_arbitrary (P : Object
Property C) [P.Nonempty] : P P.arbitrary
-/
instance nonempty_sup_right [Q.Nonempty] : (P ⊔ Q).Nonempty :=
  nonempty_of_prop (Or.inr Q.prop_arbitrary)
/-
**CategoryTheory.ObjectProperty.nonempty_top** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：nonempty_top [Nonempty C] : (⊤ : ObjectProperty C).Nonempty
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.nonempty_of_prop`：nonempty_of_prop {P : Ob
jectProperty C} {X : C} (h : P X) : P.Nonempty
-/
instance nonempty_top [Nonempty C] : (⊤ : ObjectProperty C).Nonempty :=
  nonempty_of_prop (X := Classical.arbitrary C) (by trivial)
/-
**CategoryTheory.ObjectProperty.isoClosure_sup** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：isoClosure_sup : (P ⊔ Q).isoClosure = P.isoClosure ⊔ Q.isoClosure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.monotone_isoClosure`：monotone_isoClosure (
h : P <= Q) : isoClosure P <= isoClosure Q
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma isoClosure_sup : (P ⊔ Q).isoClosure = P.isoClosure ⊔ Q.isoClosure := by
  ext X
  simp only [prop_sup_iff]
  constructor
  · rintro ⟨Y, hY, ⟨e⟩⟩
    simp only [prop_sup_iff] at hY
    obtain hY | hY := hY
    · exact Or.inl ⟨Y, hY, ⟨e⟩⟩
    · exact Or.inr ⟨Y, hY, ⟨e⟩⟩
  · rintro (hY | hY)
    · exact monotone_isoClosure le_sup_left _ hY
    · exact monotone_isoClosure le_sup_right _ hY
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms] :
    (P ⊔ Q).IsClosedUnderIsomorphisms := by
  simp only [isClosedUnderIsomorphisms_iff_isoClosure_eq_self, isoClosure_sup, isoClosure_eq_self]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms] :
    IsClosedUnderIsomorphisms (P ⊓ Q) where
  of_iso e h := ⟨IsClosedUnderIsomorphisms.of_iso e h.1, IsClosedUnderIsomorphisms.of_iso e h.2⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsClosedUnderIsomorphisms (⊥ : ObjectProperty C) where
  of_iso _ h := h
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsClosedUnderIsomorphisms (⊤ : ObjectProperty C) where
  of_iso := by simp

end

section

variable {α : Sort*} (P : α → ObjectProperty C) (X : C)

/-
**CategoryTheory.ObjectProperty.prop_iSup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {α : Sort u_1} (P
 : α → CategoryTheory.ObjectProperty C)   (X : C), (⨆ a, P a) X ↔ ∃ a, P a X
参数：P : α → CategoryTheory.ObjectProperty C；X : C；⨆ a, P a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `iSup_Prop_eq`：iSup_Prop_eq {p : ι -> Prop} : ⨆ i, p i = exists i, p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp high] lemma prop_iSup_iff :
    (⨆ (a : α), P a) X ↔ ∃ (a : α), P a X := by simp
/-
**CategoryTheory.ObjectProperty.nonempty_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：nonempty_iSup (a : α) [(P a).Nonempty] : (⨆ a, P a).Nonempty
参数：a : α；P a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.nonempty_of_prop`：nonempty_of_prop {P : Ob
jectProperty C} {X : C} (h : P X) : P.Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.ObjectProperty.prop_iSup_iff`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {α : Sort u_1} (P : α → CategoryTheory.ObjectPrope
rty C)   (X : C), (⨆ a, P a) X ↔ …
· 使用引理 `CategoryTheory.ObjectProperty.prop_arbitrary`：prop_arbitrary (P : Object
Property C) [P.Nonempty] : P P.arbitrary
-/
lemma nonempty_iSup (a : α) [(P a).Nonempty] : (⨆ a, P a).Nonempty :=
  nonempty_of_prop ((prop_iSup_iff P _).mpr ⟨a, (P a).prop_arbitrary⟩)
/-
**CategoryTheory.ObjectProperty.isoClosure_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：isoClosure_iSup : ((⨆ (a : α), P a)).isoClosure = ⨆ (a : α), (P a).isoClos
ure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_le_iff`：isoClosure_le_iff [IsCl
osedUnderIsomorphisms Q] : isoClosure P <= Q ↔ P <= Q
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsIsoClosure`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Obje
ctProperty C),   P.isoClosure.IsClosedUnderIsomorphisms
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
-/
lemma isoClosure_iSup :
    ((⨆ (a : α), P a)).isoClosure = ⨆ (a : α), (P a).isoClosure := by
  refine le_antisymm ?_ ?_
  · rintro X ⟨Y, hY, ⟨e⟩⟩
    simp only [prop_iSup_iff] at hY ⊢
    obtain ⟨a, hY⟩ := hY
    exact ⟨a, _, hY, ⟨e⟩⟩
  · simp only [iSup_le_iff]
    intro a
    rw [isoClosure_le_iff]
    exact (le_iSup P a).trans (le_isoClosure _)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ a, (P a).IsClosedUnderIsomorphisms] :
    ((⨆ (a : α), P a)).IsClosedUnderIsomorphisms := by
  simp only [isClosedUnderIsomorphisms_iff_isoClosure_eq_self,
    isoClosure_iSup, isoClosure_eq_self]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ a, (P a).IsClosedUnderIsomorphisms] :
    ((⨅ (a : α), P a)).IsClosedUnderIsomorphisms where
  of_iso e h := by
    simp only [iInf_apply, iInf_Prop_eq] at h ⊢
    intro a
    exact (P a).prop_of_iso e (h a)

end

@[push]
/-
**CategoryTheory.ObjectProperty.ne_bot_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：ne_bot_iff_exists (P : ObjectProperty C) : ¬ P = ⊥ ↔ exists X, P X
参数：P : ObjectProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ne_bot_iff_exists (P : ObjectProperty C) : ¬ P = ⊥ ↔ ∃ X, P X := by
  simp [← le_bot_iff, not_le_iff_exists]
/-
**CategoryTheory.ObjectProperty.nonempty_iff_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：nonempty_iff_ne_bot (P : ObjectProperty C) : P.Nonempty ↔ ¬ P = ⊥
参数：P : ObjectProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.ne_bot_iff_exists`：ne_bot_iff_exists (P : 
ObjectProperty C) : ¬ P = ⊥ ↔ exists X, P X
· 使用定理 `CategoryTheory.ObjectProperty.nonempty_iff`：∀ {C : Type u} [inst : Categ
oryTheory.CategoryStruct.{v, u} C] (P : CategoryTheory.ObjectProperty C),   P.No
nempty ↔ ∃ X, P X
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonempty_iff_ne_bot (P : ObjectProperty C) : P.Nonempty ↔ ¬ P = ⊥ := by
  rw [ne_bot_iff_exists, nonempty_iff]

@[push]
/-
**CategoryTheory.ObjectProperty.not_nonempty_iff_eq_bot** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：not_nonempty_iff_eq_bot (P : ObjectProperty C) : ¬ P.Nonempty ↔ P = ⊥
参数：P : ObjectProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.nonempty_iff_ne_bot`：nonempty_iff_ne_bot (
P : ObjectProperty C) : P.Nonempty ↔ ¬ P = ⊥
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma not_nonempty_iff_eq_bot (P : ObjectProperty C) : ¬ P.Nonempty ↔ P = ⊥ := by
  rw [P.nonempty_iff_ne_bot, not_not]

@[simp]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_map_top (P : ObjectProperty C) :
    (⊤ : ObjectProperty _).map P.ι = P.isoClosure := by
  ext X
  constructor
  · rintro ⟨⟨Y, hY⟩, _, ⟨e⟩⟩
    exact ⟨Y, hY, ⟨e.symm⟩⟩
  · rintro ⟨Y, hY, ⟨e⟩⟩
    exact ⟨⟨Y, hY⟩, by simp, ⟨e.symm⟩⟩

end CategoryTheory.ObjectProperty

