/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Iso
public import Mathlib.Order.Basic

/-!
# Properties of objects in a category

Given a category `C`, we introduce an abbreviation `ObjectProperty C`
for predicates `C → Prop`.

## TODO

* refactor the file `Limits.FullSubcategory` in order to rename `ClosedUnderLimitsOfShape`
  as `ObjectProperty.IsClosedUnderLimitsOfShape` (and make it a type class)
* refactor the file `Triangulated.Subcategory` in order to make it a type class
  regarding terms in `ObjectProperty C` when `C` is pretriangulated

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

/-- A property of objects in a category `C` is a predicate `C → Prop`. -/
@[nolint unusedArguments]
/-
**CategoryTheory.ObjectProperty** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：ObjectProperty (C : Type u) [CategoryStruct.{v} C] : Type u
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of objects in a category `C` is a predicate `C → Prop`.
-/
abbrev ObjectProperty (C : Type u) [CategoryStruct.{v} C] : Type u := C → Prop

namespace ObjectProperty

variable {C : Type u} {D : Type u'}

section

variable [CategoryStruct.{v} C] [CategoryStruct.{v'} D]

/-
**CategoryTheory.ObjectProperty.le_def** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ObjectProperty`。
形式化陈述：le_def {P Q : ObjectProperty C} : P <= Q ↔ forall (X : C), P X -> Q X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def {P Q : ObjectProperty C} :
    P ≤ Q ↔ ∀ (X : C), P X → Q X := Iff.rfl

@[push]
/-
**CategoryTheory.ObjectProperty.not_le_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：not_le_iff_exists {P Q : ObjectProperty C} : ¬ P <= Q ↔ exists (X : C), P 
X ∧ ¬ Q X
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma not_le_iff_exists {P Q : ObjectProperty C} :
    ¬ P ≤ Q ↔ ∃ (X : C), P X ∧ ¬ Q X := by
  simp [le_def]

/-- The typeclass associated to `P : ObjectProperty C`. -/
@[mk_iff]
/-
**CategoryTheory.ObjectProperty.Is** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.O
bjectProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.CategoryStruct.{v, u} C] → CategoryT
heory.ObjectProperty C → C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The typeclass associated to `P : ObjectProperty C`.
-/
class Is (P : ObjectProperty C) (X : C) : Prop where
  prop : P X
/-
**CategoryTheory.ObjectProperty.prop_of_is** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ObjectProperty`。
形式化陈述：prop_of_is (P : ObjectProperty C) (X : C) [P.Is X] : P X
参数：P : ObjectProperty C；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ObjectProperty.is_iff`：∀ {C : Type u} [inst : CategoryThe
ory.CategoryStruct.{v, u} C] (P : CategoryTheory.ObjectProperty C) (X : C),   P.
Is X ↔ P X
-/
lemma prop_of_is (P : ObjectProperty C) (X : C) [P.Is X] : P X := by rwa [← P.is_iff]
/-
**CategoryTheory.ObjectProperty.is_of_prop** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ObjectProperty`。
形式化陈述：is_of_prop (P : ObjectProperty C) {X : C} (hX : P X) : P.Is X
参数：P : ObjectProperty C；hX : P X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.is_iff`：∀ {C : Type u} [inst : CategoryThe
ory.CategoryStruct.{v, u} C] (P : CategoryTheory.ObjectProperty C) (X : C),   P.
Is X ↔ P X
-/
lemma is_of_prop (P : ObjectProperty C) {X : C} (hX : P X) : P.Is X := by rwa [P.is_iff]

/-- `Nonempty P` is a typeclass saying there exists an object `X : C` that satisfies `P`. -/
@[mk_iff]
/-
**CategoryTheory.ObjectProperty.Nonempty** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.ObjectProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.CategoryStruct.{v, u} C] → CategoryT
heory.ObjectProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nonempty P` is a typeclass saying there exists an object `X : C` that satisfies
 `P`.
-/
protected class Nonempty (P : ObjectProperty C) : Prop where
  exists_prop : ∃ X, P X
/-
**CategoryTheory.ObjectProperty.exists_prop_of_nonempty** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：exists_prop_of_nonempty (P : ObjectProperty C) [P.Nonempty] : exists X, P 
X
参数：P : ObjectProperty C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.Nonempty.exists_prop`：∀ {C : Type u} {inst
 : CategoryTheory.CategoryStruct.{v, u} C} {P : CategoryTheory.ObjectProperty C}
   [self : P.Nonempty], ∃ X, P X
-/
lemma exists_prop_of_nonempty (P : ObjectProperty C) [P.Nonempty] : ∃ X, P X :=
  Nonempty.exists_prop
/-
**CategoryTheory.ObjectProperty.nonempty_of_prop** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：nonempty_of_prop {P : ObjectProperty C} {X : C} (h : P X) : P.Nonempty
参数：h : P X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nonempty_of_prop {P : ObjectProperty C} {X : C} (h : P X) : P.Nonempty := ⟨X, h⟩

/-- Using `Classical.choice`, extracts an object from a `Nonempty` object property. -/
/-
**CategoryTheory.ObjectProperty.arbitrary** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ObjectProperty`。
形式化陈述：arbitrary (P : ObjectProperty C) [P.Nonempty] : C
参数：P : ObjectProperty C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.exists_prop_of_nonempty`：exists_prop_of_no
nempty (P : ObjectProperty C) [P.Nonempty] : exists X, P X

--- 原说明 ---
Using `Classical.choice`, extracts an object from a `Nonempty` object property.
-/
noncomputable def arbitrary (P : ObjectProperty C) [P.Nonempty] : C :=
  (exists_prop_of_nonempty P).choose
/-
**CategoryTheory.ObjectProperty.prop_arbitrary** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：prop_arbitrary (P : ObjectProperty C) [P.Nonempty] : P P.arbitrary
参数：P : ObjectProperty C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `CategoryTheory.ObjectProperty.exists_prop_of_nonempty`：exists_prop_of_no
nempty (P : ObjectProperty C) [P.Nonempty] : exists X, P X
-/
lemma prop_arbitrary (P : ObjectProperty C) [P.Nonempty] : P P.arbitrary :=
  (exists_prop_of_nonempty P).choose_spec
/-
**CategoryTheory.ObjectProperty.Nonempty.mono** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ObjectProperty.Nonempty`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.CategoryStruct.{v, u} C] {P Q : Cate
goryTheory.ObjectProperty C} [P.Nonempty],   P ≤ Q → Q.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.nonempty_of_prop`：nonempty_of_prop {P : Ob
jectProperty C} {X : C} (h : P X) : P.Nonempty
· 使用引理 `CategoryTheory.ObjectProperty.prop_arbitrary`：prop_arbitrary (P : Object
Property C) [P.Nonempty] : P P.arbitrary
-/
lemma Nonempty.mono {P Q : ObjectProperty C} [P.Nonempty] (hPQ : P ≤ Q) : Q.Nonempty :=
  nonempty_of_prop (hPQ _ P.prop_arbitrary)
/-
**CategoryTheory.ObjectProperty.nonempty_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：nonempty_of_lt {P Q : ObjectProperty C} (h : P < Q) : Q.Nonempty
参数：h : P < Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.nonempty_of_prop`：nonempty_of_prop {P : Ob
jectProperty C} {X : C} (h : P X) : P.Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ObjectProperty.not_le_iff_exists`：not_le_iff_exists {P Q 
: ObjectProperty C} : ¬ P <= Q ↔ exists (X : C), P X ∧ ¬ Q X
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma nonempty_of_lt {P Q : ObjectProperty C} (h : P < Q) : Q.Nonempty :=
  nonempty_of_prop (not_le_iff_exists.mp (not_le_of_gt h)).choose_spec.1

section

variable {ι : Type u'} (X : ι → C)

/-- The property of objects that is satisfied by the `X i` for a family
of objects `X : ι : C`. -/
/-
**CategoryTheory.ObjectProperty.ofObj** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y.ObjectProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.CategoryStruct.{v, u} C] → {ι : Ty
pe u'} → (ι → C) → CategoryTheory.ObjectProperty C
参数：ι → C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects that is satisfied by the `X i` for a family
of objects `X : ι : C`.
-/
inductive ofObj : ObjectProperty C
  | mk (i : ι) : ofObj (X i)

@[simp]
/-
**CategoryTheory.ObjectProperty.ofObj_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：ofObj_apply (i : ι) : ofObj X (X i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofObj_apply (i : ι) : ofObj X (X i) := ⟨i⟩
/-
**CategoryTheory.ObjectProperty.ofObj_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ObjectProperty`。
形式化陈述：ofObj_iff (Y : C) : ofObj X Y ↔ exists i, X i = Y
参数：Y : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ofObj_iff (Y : C) : ofObj X Y ↔ ∃ i, X i = Y := by
  constructor
  · rintro ⟨i⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i⟩
/-
**CategoryTheory.ObjectProperty.ofObj_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：ofObj_le_iff (P : ObjectProperty C) : ofObj X <= P ↔ forall i, P (X i)
参数：P : ObjectProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ofObj_le_iff (P : ObjectProperty C) :
    ofObj X ≤ P ↔ ∀ i, P (X i) :=
  ⟨fun h i ↦ h _ (by simp), fun h ↦ by rintro _ ⟨i⟩; exact h i⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty ι] : (ofObj X).Nonempty :=
  nonempty_of_prop (ofObj_apply X (Classical.arbitrary ι))

end

@[simp]
/-
**CategoryTheory.ObjectProperty.ofObj_subtypeVal** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：ofObj_subtypeVal (P : ObjectProperty C) : ofObj (Subtype.val : Subtype P -
> C) = P
参数：P : ObjectProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.ofObj_apply`：ofObj_apply (i : ι) : ofObj X
 (X i)
-/
lemma ofObj_subtypeVal (P : ObjectProperty C) :
    ofObj (Subtype.val : Subtype P → C) = P := by
  ext X
  exact ⟨by rintro ⟨X, hX⟩; exact hX,
    fun hX ↦ ofObj_apply Subtype.val ⟨X, hX⟩⟩

/-- The property of objects in a category that is satisfied by a single object `X : C`. -/
/-
**CategoryTheory.ObjectProperty.singleton** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：singleton (X : C) : ObjectProperty C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects in a category that is satisfied by a single object `X : 
C`.
-/
abbrev singleton (X : C) : ObjectProperty C := ofObj (fun (_ : Unit) ↦ X)

@[simp]
/-
**CategoryTheory.ObjectProperty.singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：singleton_iff (X Y : C) : singleton X Y ↔ X = Y
参数：X Y : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma singleton_iff (X Y : C) : singleton X Y ↔ X = Y := by simp [ofObj_iff]

@[simp]
/-
**CategoryTheory.ObjectProperty.singleton_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：singleton_le_iff {X : C} {P : ObjectProperty C} : singleton X <= P ↔ P X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma singleton_le_iff {X : C} {P : ObjectProperty C} :
    singleton X ≤ P ↔ P X := by
  simp [ofObj_le_iff]

/-- The property of objects in a category that is satisfied by `X : C` and `Y : C`. -/
/-
**CategoryTheory.ObjectProperty.pair** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.O
bjectProperty`。
形式化陈述：pair (X Y : C) : ObjectProperty C
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects in a category that is satisfied by `X : C` and `Y : C`.
-/
def pair (X Y : C) : ObjectProperty C :=
  ofObj (Sum.elim (fun (_ : Unit) ↦ X) (fun (_ : Unit) ↦ Y))

@[simp]
/-
**CategoryTheory.ObjectProperty.pair_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ObjectProperty`。
形式化陈述：pair_iff (X Y Z : C) : pair X Y Z ↔ X = Z ∨ Y = Z
参数：X Y Z : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pair_iff (X Y Z : C) :
    pair X Y Z ↔ X = Z ∨ Y = Z := by
  constructor
  · rintro ⟨_ | _⟩ <;> tauto
  · rintro (rfl | rfl); exacts [⟨Sum.inl .unit⟩, ⟨Sum.inr .unit⟩]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : C) : (pair X Y).Nonempty := inferInstanceAs (ofObj _).Nonempty

end

section

variable [Category.{v} C] [Category.{v'} D]

/-- The inverse image of a property of objects by a functor. -/
/-
**CategoryTheory.ObjectProperty.inverseImage** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：inverseImage (P : ObjectProperty D) (F : C ⥤ D) : ObjectProperty C
参数：P : ObjectProperty D；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse image of a property of objects by a functor.
-/
def inverseImage (P : ObjectProperty D) (F : C ⥤ D) : ObjectProperty C :=
  fun X ↦ P (F.obj X)

@[simp]
/-
**CategoryTheory.ObjectProperty.prop_inverseImage_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：prop_inverseImage_iff (P : ObjectProperty D) (F : C ⥤ D) (X : C) : P.inver
seImage F X ↔ P (F.obj X)
参数：P : ObjectProperty D；F : C ⥤ D；X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma prop_inverseImage_iff (P : ObjectProperty D) (F : C ⥤ D) (X : C) :
    P.inverseImage F X ↔ P (F.obj X) := Iff.rfl

/-- The essential image of a property of objects by a functor. -/
/-
**CategoryTheory.ObjectProperty.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ob
jectProperty`。
形式化陈述：map (P : ObjectProperty C) (F : C ⥤ D) : ObjectProperty D
参数：P : ObjectProperty C；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The essential image of a property of objects by a functor.
-/
def map (P : ObjectProperty C) (F : C ⥤ D) : ObjectProperty D :=
  fun Y ↦ ∃ (X : C), P X ∧ Nonempty (F.obj X ≅ Y)
/-
**CategoryTheory.ObjectProperty.prop_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：prop_map_iff (P : ObjectProperty C) (F : C ⥤ D) (Y : D) : P.map F Y ↔ exis
ts (X : C), P X ∧ Nonempty (F.obj X ≅ Y)
参数：P : ObjectProperty C；F : C ⥤ D；Y : D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma prop_map_iff (P : ObjectProperty C) (F : C ⥤ D) (Y : D) :
    P.map F Y ↔ ∃ (X : C), P X ∧ Nonempty (F.obj X ≅ Y) := Iff.rfl
/-
**CategoryTheory.ObjectProperty.prop_map_obj** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：prop_map_obj (P : ObjectProperty C) (F : C ⥤ D) {X : C} (hX : P X) : P.map
 F (F.obj X)
参数：P : ObjectProperty C；F : C ⥤ D；hX : P X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prop_map_obj (P : ObjectProperty C) (F : C ⥤ D) {X : C} (hX : P X) :
    P.map F (F.obj X) :=
  ⟨X, hX, ⟨Iso.refl _⟩⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) (F : C ⥤ D) [P.Nonempty] : (P.map F).Nonempty :=
  nonempty_of_prop (P.prop_map_obj F P.prop_arbitrary)
/-
**CategoryTheory.ObjectProperty.map_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：map_monotone {P Q : ObjectProperty C} (h : P <= Q) (F : C ⥤ D) : P.map F <
= Q.map F
参数：h : P <= Q；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_monotone {P Q : ObjectProperty C} (h : P ≤ Q) (F : C ⥤ D) :
    P.map F ≤ Q.map F := by
  rintro X ⟨Y, hY, ⟨e⟩⟩
  exact ⟨Y, h _ hY, ⟨e⟩⟩

/-- The strict image of a property of objects by a functor. -/
/-
**CategoryTheory.ObjectProperty.strictMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：{C : Type u} →   {D : Type u'} →     [inst : CategoryTheory.Category.{v, u
} C] →       [inst_1 : CategoryTheory.Category.{v', u'} D] →         CategoryThe
ory.ObjectProperty C → CategoryTheory.Functor C D → CategoryTheory.ObjectPropert
y D
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The strict image of a property of objects by a functor.
-/
inductive strictMap (P : ObjectProperty C) (F : C ⥤ D) : ObjectProperty D
  | mk (X : C) (hX : P X) : strictMap P F (F.obj X)
/-
**CategoryTheory.ObjectProperty.strictMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：strictMap_iff (P : ObjectProperty C) (F : C ⥤ D) (Y : D) : P.strictMap F Y
 ↔ exists (X : C), P X ∧ F.obj X = Y
参数：P : ObjectProperty C；F : C ⥤ D；Y : D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma strictMap_iff (P : ObjectProperty C) (F : C ⥤ D) (Y : D) :
    P.strictMap F Y ↔ ∃ (X : C), P X ∧ F.obj X = Y :=
  ⟨by rintro ⟨X, hX⟩; exact ⟨X, hX, rfl⟩, by rintro ⟨X, hX, rfl⟩; exact ⟨X, hX⟩⟩
/-
**CategoryTheory.ObjectProperty.strictMap_obj** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：strictMap_obj (P : ObjectProperty C) (F : C ⥤ D) {X : C} (hX : P X) : P.st
rictMap F (F.obj X)
参数：P : ObjectProperty C；F : C ⥤ D；hX : P X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma strictMap_obj (P : ObjectProperty C) (F : C ⥤ D) {X : C} (hX : P X) :
    P.strictMap F (F.obj X) :=
  ⟨X, hX⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) (F : C ⥤ D) [P.Nonempty] : (P.strictMap F).Nonempty :=
  nonempty_of_prop (P.strictMap_obj F P.prop_arbitrary)
/-
**CategoryTheory.ObjectProperty.strictMap_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：strictMap_monotone {P Q : ObjectProperty C} (h : P <= Q) (F : C ⥤ D) : P.s
trictMap F <= Q.strictMap F
参数：h : P <= Q；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma strictMap_monotone {P Q : ObjectProperty C} (h : P ≤ Q) (F : C ⥤ D) :
    P.strictMap F ≤ Q.strictMap F := by
  rintro _ ⟨X, hX⟩
  exact ⟨X, h _ hX⟩
/-
**CategoryTheory.ObjectProperty.strictMap_le_map** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：strictMap_le_map (P : ObjectProperty C) (F : C ⥤ D) : P.strictMap F <= P.m
ap F
参数：P : ObjectProperty C；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma strictMap_le_map (P : ObjectProperty C) (F : C ⥤ D) :
    P.strictMap F ≤ P.map F := by
  rintro _ ⟨X, hX⟩
  exact ⟨X, hX, ⟨Iso.refl _⟩⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.strictMap_ofObj** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：strictMap_ofObj {ι : Type u'} (X : ι -> C) (F : C ⥤ D) : (ofObj X).strictM
ap F = ofObj (F.obj ∘ X)
参数：X : ι -> C；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma strictMap_ofObj {ι : Type u'} (X : ι → C) (F : C ⥤ D) :
    (ofObj X).strictMap F = ofObj (F.obj ∘ X) := by
  ext Y
  simp [ofObj_iff, strictMap_iff]

@[simp high]
/-
**CategoryTheory.ObjectProperty.strictMap_singleton** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：strictMap_singleton (X : C) (F : C ⥤ D) : (singleton X).strictMap F = sing
leton (F.obj X)
参数：X : C；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma strictMap_singleton (X : C) (F : C ⥤ D) :
    (singleton X).strictMap F = singleton (F.obj X) := by
  ext
  simp [strictMap_iff]

end

end ObjectProperty

end CategoryTheory

