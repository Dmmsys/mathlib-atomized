/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Smallness of a property of objects

In this file, given `P : ObjectProperty C`, we define
`ObjectProperty.Small.{w} P` as an abbreviation for `Small.{w} (Subtype P)`.

-/

public section

universe w' w v v' u u'

namespace CategoryTheory.ObjectProperty

open Opposite

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A property of objects is small relative to a universe `w`
if the corresponding subtype is. -/
@[pp_with_univ]
/-
**CategoryTheory.ObjectProperty.Small** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
ObjectProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
ObjectProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of objects is small relative to a universe `w`
if the corresponding subtype is.
-/
protected abbrev Small (P : ObjectProperty C) : Prop := _root_.Small.{w} (Subtype P)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    Small.{w} P.FullSubcategory :=
  small_of_surjective (f := fun (x : Subtype P) ↦ ⟨x.1, x.2⟩) (fun x ↦ ⟨⟨x.1, x.2⟩, rfl⟩)
/-
**CategoryTheory.ObjectProperty.Small.of_le** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.ObjectProperty.Small`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTh
eory.ObjectProperty C}   [CategoryTheory.ObjectProperty.Small.{w, v, u} Q], P ≤ 
Q → CategoryTheory.ObjectProperty.Small.{w, v, u} P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `Subtype.map_injective`：map_injective {p : α -> Prop} {q : β -> Prop} {f 
: α -> β} (h : forall a, p a -> q (f a)) (hf : Injective f) : Injective (map f h
)
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
lemma Small.of_le {P Q : ObjectProperty C} [ObjectProperty.Small.{w} Q] (h : P ≤ Q) :
    ObjectProperty.Small.{w} P :=
  small_of_injective (Subtype.map_injective h Function.injective_id)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} P.op :=
  small_of_injective P.subtypeOpEquiv.injective
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty Cᵒᵖ) [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} P.unop := by
  simpa only [← small_congr P.unop.subtypeOpEquiv]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} (X : ι → C) [Small.{w} ι] :
    ObjectProperty.Small.{w} (ofObj X) :=
  small_of_surjective (f := fun i ↦ ⟨X i, by simp⟩) (by rintro ⟨_, ⟨i⟩⟩; simp)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : C) : ObjectProperty.Small.{w} (.pair X Y) := by
  dsimp [pair]
  infer_instance
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P Q : ObjectProperty C} [ObjectProperty.Small.{w} Q] :
    ObjectProperty.Small.{w} (P ⊓ Q) :=
  Small.of_le inf_le_right
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P Q : ObjectProperty C} [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} (P ⊓ Q) :=
  Small.of_le inf_le_left
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P Q : ObjectProperty C} [ObjectProperty.Small.{w} P] [ObjectProperty.Small.{w} Q] :
    ObjectProperty.Small.{w} (P ⊔ Q) :=
  small_of_surjective (f := fun (x : Subtype P ⊕ Subtype Q) ↦ match x with
      | .inl x => ⟨x.1, Or.inl x.2⟩
      | .inr x => ⟨x.1, Or.inr x.2⟩)
    (by rintro ⟨x, hx | hx⟩ <;> aesop)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} (P : α → ObjectProperty C)
    [∀ a, ObjectProperty.Small.{w} (P a)] [Small.{w} α] :
    ObjectProperty.Small.{w} (⨆ a, P a) :=
  small_of_surjective (f := fun (x : Σ a, Subtype (P a)) ↦ ⟨x.2.1, by aesop⟩)
    (fun ⟨x, hx⟩ ↦ by aesop)

@[simp]
/-
**CategoryTheory.ObjectProperty.small_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：small_op_iff (P : ObjectProperty C) : ObjectProperty.Small.{w} P.op ↔ Obje
ctProperty.Small.{w} P
参数：P : ObjectProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_congr`：small_congr {α : Type*} {β : Type*} (e : α ≃ β) : Small.{w}
 α ↔ Small.{w} β
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma small_op_iff (P : ObjectProperty C) :
    ObjectProperty.Small.{w} P.op ↔ ObjectProperty.Small.{w} P :=
  small_congr
    { toFun x := ⟨x.1.unop, x.2⟩
      invFun x := ⟨op x.1, x.2⟩}

@[simp]
/-
**CategoryTheory.ObjectProperty.small_unop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：small_unop_iff (P : ObjectProperty Cᵒᵖ) : ObjectProperty.Small.{w} P.unop 
↔ ObjectProperty.Small.{w} P
参数：P : ObjectProperty Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.small_op_iff`：small_op_iff (P : ObjectProp
erty C) : ObjectProperty.Small.{w} P.op ↔ ObjectProperty.Small.{w} P
· 使用引理 `CategoryTheory.ObjectProperty.op_unop`：op_unop (P : ObjectProperty Cᵒᵖ) 
: P.unop.op = P
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma small_unop_iff (P : ObjectProperty Cᵒᵖ) :
    ObjectProperty.Small.{w} P.unop ↔ ObjectProperty.Small.{w} P := by
  rw [← small_op_iff, op_unop]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} P.op := by
  simpa
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty Cᵒᵖ) [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} P.unop := by
  simpa

/-- A property of objects is essentially small relative to a universe `w`
if it is contained in the closure by isomorphisms of a small property. -/
@[pp_with_univ]
/-
**CategoryTheory.ObjectProperty.EssentiallySmall** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
ObjectProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of objects is essentially small relative to a universe `w`
if it is contained in the closure by isomorphisms of a small property.
-/
protected class EssentiallySmall (P : ObjectProperty C) : Prop where
  exists_small_le' (P) : ∃ (Q : ObjectProperty C) (_ : ObjectProperty.Small.{w} Q),
    P ≤ Q.isoClosure
/-
**CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.ObjectProperty.EssentiallySmall`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.ObjectProperty C)   [CategoryTheory.ObjectProperty.EssentiallySmall.{w, v, u}
 P],   ∃ Q, ∃ (_ : CategoryTheory.ObjectProperty.Small.{w, v, u} Q), Q ≤ P ∧ P ≤
 Q.isoClosure
参数：P : CategoryTheory.ObjectProperty C；_ : CategoryTheory.ObjectProperty.Small.{
w, v, u} Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le'`：∀ {C : 
Type u} {inst : CategoryTheory.Category.{v, u} C} (P : CategoryTheory.ObjectProp
erty C)   [self : CategoryTheory.ObjectProperty.Essen…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `CategoryTheory.ObjectProperty.instSmallMin_1`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {P Q : CategoryTheory.ObjectProperty C}   [Catego
ryTheory.ObjectProperty.Small.{w, …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma EssentiallySmall.exists_small_le (P : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{w} P] :
    ∃ (Q : ObjectProperty C) (_ : ObjectProperty.Small.{w} Q), Q ≤ P ∧ P ≤ Q.isoClosure := by
  obtain ⟨Q, _, hQ⟩ := exists_small_le' P
  let P' := Q ⊓ P.isoClosure
  have h (X' : Subtype P') : ∃ (X : Subtype P), Nonempty (X'.1 ≅ X.1) :=
    ⟨⟨X'.2.2.choose, X'.2.2.choose_spec.choose⟩, X'.2.2.choose_spec.choose_spec⟩
  choose φ hφ using h
  refine ⟨fun X ↦ X ∈ Set.range (Subtype.val ∘ φ), ?_, ?_, ?_⟩
  · exact small_of_surjective (f := fun X ↦ ⟨(φ X).1, by tauto⟩)
      (by rintro ⟨_, Z, rfl⟩; exact ⟨Z, rfl⟩)
  · intro X hX
    simp only [Set.mem_range, Function.comp_apply, Subtype.exists] at hX
    obtain ⟨Y, hY, rfl⟩ := hX
    exact (φ ⟨Y, hY⟩).2
  · intro X hX
    obtain ⟨Y, hY, ⟨e⟩⟩ := hQ _ hX
    let Z : Subtype P' := ⟨Y, hY, ⟨X, hX, ⟨e.symm⟩⟩⟩
    exact ⟨_, ⟨Z, rfl⟩, ⟨e ≪≫ (hφ Z).some⟩⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    ObjectProperty.EssentiallySmall.{w} P where
  exists_small_le' := ⟨P, inferInstance, le_isoClosure P⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{w} P] :
    ObjectProperty.EssentiallySmall.{w} P.isoClosure where
  exists_small_le' := by
    obtain ⟨Q, _, _, _⟩ := EssentiallySmall.exists_small_le.{w} P
    exact ⟨Q, inferInstance, by rwa [isoClosure_le_iff]⟩
/-
**CategoryTheory.ObjectProperty.EssentiallySmall.exists_small** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ObjectProperty.EssentiallySmall`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.ObjectProperty C)   [P.IsClosedUnderIsomorphisms] [CategoryTheory.ObjectPrope
rty.EssentiallySmall.{w, v, u} P],   ∃ P₀, ∃ (_ : CategoryTheory.ObjectProperty.
Small.{w, v, u} P₀), P = P₀.isoClosure
参数：P : CategoryTheory.ObjectProperty C；_ : CategoryTheory.ObjectProperty.Small.{
w, v, u} P₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectPrope
rty C)   [CategoryTheory.ObjectProperty.EssentiallyS…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_le_iff`：isoClosure_le_iff [IsCl
osedUnderIsomorphisms Q] : isoClosure P <= Q ↔ P <= Q
-/
lemma EssentiallySmall.exists_small (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [ObjectProperty.EssentiallySmall.{w} P] :
    ∃ (P₀ : ObjectProperty C) (_ : ObjectProperty.Small.{w} P₀), P = P₀.isoClosure := by
  obtain ⟨Q, _, hQ₁, hQ₂⟩ := exists_small_le P
  exact ⟨Q, inferInstance, le_antisymm hQ₂ (by rwa [isoClosure_le_iff])⟩
/-
**CategoryTheory.ObjectProperty.EssentiallySmall.of_le** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ObjectProperty.EssentiallySmall`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTh
eory.ObjectProperty C}   [CategoryTheory.ObjectProperty.EssentiallySmall.{w, v, 
u} Q],   P ≤ Q → CategoryTheory.ObjectProperty.EssentiallySmall.{w, v, u} P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le'`：∀ {C : 
Type u} {inst : CategoryTheory.Category.{v, u} C} (P : CategoryTheory.ObjectProp
erty C)   [self : CategoryTheory.ObjectProperty.Essen…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma EssentiallySmall.of_le {P Q : ObjectProperty C}
    [ObjectProperty.EssentiallySmall.{w} Q] (h : P ≤ Q) :
    ObjectProperty.EssentiallySmall.{w} P where
  exists_small_le' := by
    obtain ⟨R, _, hR⟩ := EssentiallySmall.exists_small_le' Q
    exact ⟨R, inferInstance, h.trans hR⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P Q : ObjectProperty C}
    [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q] :
    ObjectProperty.EssentiallySmall.{w} (P ⊔ Q) := by
  obtain ⟨P', _, hP'⟩ := EssentiallySmall.exists_small_le' P
  obtain ⟨Q', _, hQ'⟩ := EssentiallySmall.exists_small_le' Q
  refine ⟨P' ⊔ Q', inferInstance, ?_⟩
  simp only [sup_le_iff]
  constructor
  · exact hP'.trans (monotone_isoClosure le_sup_left)
  · exact hQ'.trans (monotone_isoClosure le_sup_right)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} (P : α → ObjectProperty C)
    [∀ a, ObjectProperty.EssentiallySmall.{w} (P a)] [Small.{w} α] :
    ObjectProperty.EssentiallySmall.{w} (⨆ a, P a) where
  exists_small_le' := by
    have h (a : α) := EssentiallySmall.exists_small_le' (P a)
    choose Q _ hQ using h
    refine ⟨⨆ a, Q a, inferInstance, ?_⟩
    simp only [iSup_le_iff]
    intro a
    exact (hQ a).trans (monotone_isoClosure (le_iSup Q a))

@[simp]
/-
**CategoryTheory.ObjectProperty.essentiallySmall_op_iff** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：essentiallySmall_op_iff (P : ObjectProperty C) : ObjectProperty.Essentiall
ySmall.{w} P.op ↔ ObjectProperty.EssentiallySmall.{w} P
参数：P : ObjectProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectPrope
rty C)   [CategoryTheory.ObjectProperty.EssentiallyS…
· 使用定理 `CategoryTheory.ObjectProperty.instSmallUnopOfOpposite_1`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProperty Cᵒᵖ
)   [CategoryTheory.ObjectProperty.Small.{w, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.unop_isoClosure`：unop_isoClosure (P : Obje
ctProperty Cᵒᵖ) : P.isoClosure.unop = P.unop.isoClosure
· 使用引理 `CategoryTheory.ObjectProperty.op_monotone_iff`：op_monotone_iff {P Q : Ob
jectProperty C} : P.op <= Q.op ↔ P <= Q
· 使用引理 `CategoryTheory.ObjectProperty.op_unop`：op_unop (P : ObjectProperty Cᵒᵖ) 
: P.unop.op = P
· 使用定理 `CategoryTheory.ObjectProperty.instSmallOppositeOp_1`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProperty C)   [C
ategoryTheory.ObjectProperty.Small.{w, v,…
· 使用引理 `CategoryTheory.ObjectProperty.op_isoClosure`：op_isoClosure (P : ObjectPr
operty C) : P.isoClosure.op = P.op.isoClosure
-/
lemma essentiallySmall_op_iff (P : ObjectProperty C) :
    ObjectProperty.EssentiallySmall.{w} P.op ↔
      ObjectProperty.EssentiallySmall.{w} P := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · obtain ⟨Q, h₁, _, h₂⟩ := EssentiallySmall.exists_small_le P.op
    exact ⟨Q.unop, inferInstance, by rwa [← unop_isoClosure, ← op_monotone_iff, op_unop]⟩
  · obtain ⟨Q, h₁, _, h₂⟩ := EssentiallySmall.exists_small_le P
    exact ⟨Q.op, inferInstance, by rwa [← op_isoClosure, op_monotone_iff]⟩

@[simp]
/-
**CategoryTheory.ObjectProperty.essentiallySmall_unop_iff** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：essentiallySmall_unop_iff (P : ObjectProperty Cᵒᵖ) : ObjectProperty.Essent
iallySmall.{w} P.unop ↔ ObjectProperty.EssentiallySmall.{w} P
参数：P : ObjectProperty Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.essentiallySmall_op_iff`：essentiallySmall_
op_iff (P : ObjectProperty C) : ObjectProperty.EssentiallySmall.{w} P.op ↔ Objec
tProperty.EssentiallySmall.{w} P
· 使用引理 `CategoryTheory.ObjectProperty.op_unop`：op_unop (P : ObjectProperty Cᵒᵖ) 
: P.unop.op = P
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma essentiallySmall_unop_iff (P : ObjectProperty Cᵒᵖ) :
    ObjectProperty.EssentiallySmall.{w} P.unop ↔
      ObjectProperty.EssentiallySmall.{w} P := by
  rw [← essentiallySmall_op_iff, op_unop]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{w} P] :
    ObjectProperty.EssentiallySmall.{w} P.op := by
  simpa
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty Cᵒᵖ) [ObjectProperty.EssentiallySmall.{w} P] :
    ObjectProperty.EssentiallySmall.{w} P.unop := by
  simpa
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [LocallySmall.{w} C]
    [ObjectProperty.EssentiallySmall.{w} P] : EssentiallySmall.{w} P.FullSubcategory := by
  obtain ⟨Q, _, h₁, h₂⟩ := EssentiallySmall.exists_small_le P
  have := (isEquivalence_ιOfLE_iff h₁).2 h₂
  rw [← essentiallySmall_congr (ιOfLE h₁).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EssentiallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} (⊤ : ObjectProperty C) where
  exists_small_le' :=
    ⟨ofObj (equivSmallModel.{w} C).inverse.obj, inferInstance,
      fun X _ ↦ ⟨_, ⟨_⟩, ⟨(equivSmallModel.{w} C).unitIso.app X⟩⟩⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] (F : C ⥤ D) :
    ObjectProperty.Small.{w} (P.strictMap F) :=
  small_of_surjective (f := fun (X : Subtype P) ↦ ⟨F.obj X.1, ⟨_, X.2⟩⟩) (by
    rintro ⟨_, ⟨X, hX⟩⟩
    exact ⟨⟨X, hX⟩, rfl⟩)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{w} P]
    (F : C ⥤ D) : ObjectProperty.EssentiallySmall.{w} (P.map F) := by
  obtain ⟨Q, _, h₁, h₂⟩ := EssentiallySmall.exists_small_le P
  exact ⟨Q.strictMap F, inferInstance, (map_monotone h₂ F).trans (by simp)⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EssentiallySmall.{w} C] (F : C ⥤ D) :
    ObjectProperty.EssentiallySmall.{w} F.essImage := by
  rw [← ObjectProperty.map_top]
  infer_instance
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : ObjectProperty C) [LocallySmall.{w} C]
    [ObjectProperty.EssentiallySmall.{w} P] : EssentiallySmall.{w} P.FullSubcategory := by
  obtain ⟨Q, _, h₁, h₂⟩ := EssentiallySmall.exists_small_le P
  have := (isEquivalence_ιOfLE_iff h₁).2 h₂
  rw [← essentiallySmall_congr (ιOfLE h₁).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _
/-
**CategoryTheory.ObjectProperty.EssentiallySmall.of_functor** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ObjectProperty.EssentiallySmall`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   (P : CategoryTheory.ObjectProperty 
C) (F : CategoryTheory.Functor C D),   CategoryTheory.ObjectProperty.Essentially
Small.{w, v', u'} (P.map F) →     (∀ (Y : D), CategoryTheory.ObjectProperty.Esse
ntiallySmall.{w, v, u} (P ⊓ fun x => Nonempty (F.obj x ≅ Y))) →       CategoryTh
eory.ObjectProperty.EssentiallySmall.{w, v, u} P
参数：P : CategoryTheory.ObjectProperty C；F : CategoryTheory.Functor C D；P.map F；∀ 
(Y : D), CategoryTheory.ObjectProperty.EssentiallySmall.{w, v, u} (P ⊓ fun x => 
Nonempty (F.obj x ≅ Y))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.ObjectProperty.instSmallOfObjOfSmall`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {ι : Type u_1} (X : ι → C) [Small.{w, u_1}
 ι],   CategoryTheory.ObjectProperty.Smal…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le'`：∀ {C : 
Type u} {inst : CategoryTheory.Category.{v, u} C} (P : CategoryTheory.ObjectProp
erty C)   [self : CategoryTheory.ObjectProperty.Essen…
-/
lemma EssentiallySmall.of_functor (P : ObjectProperty C) (F : C ⥤ D)
    (H₁ : ObjectProperty.EssentiallySmall.{w} (P.map F))
    (H₂ : ∀ Y : D, ObjectProperty.EssentiallySmall.{w} (P ⊓ (Nonempty <| F.obj · ≅ Y))) :
    ObjectProperty.EssentiallySmall.{w} P := by
  choose P₁ hP₁ x hP₁x hx using H₁.1
  choose P₂ hP₂ y hP₂y hy using fun Y ↦ (H₂ Y).1
  let f : Subtype P → Σ i : Subtype P₁, Subtype (P₂ i.1) := fun c ↦
    ⟨⟨_, hP₁x _ _⟩, _, hP₂y _ c ⟨c.2, hx _ ⟨_, c.2, ⟨.refl _⟩⟩⟩⟩
  let g : (Σ i : Subtype P₁, Subtype (P₂ i.1)) → C := fun i ↦ i.2.1
  exact ⟨.ofObj g, inferInstance, fun X hX ↦ ⟨_, ⟨f ⟨X, hX⟩⟩, hy _ _ _⟩⟩
/-
**CategoryTheory.ObjectProperty.exists_equivalence_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：exists_equivalence_iff (P : ObjectProperty C) [LocallySmall.{w'} C] : (exi
sts (J : Type w) (_ : Category.{w'} J), Nonempty (P.FullSubcategory ≌ J)) ↔ Obje
ctProperty.EssentiallySmall.{w} P
参数：P : ObjectProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.instSmallOfObjOfSmall`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {ι : Type u_1} (X : ι → C) [Small.{w, u_1}
 ι],   CategoryTheory.ObjectProperty.Smal…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectPrope
rty C)   [CategoryTheory.ObjectProperty.EssentiallyS…
· 使用定理 `CategoryTheory.ObjectProperty.instSmallFullSubcategoryOfSmall`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [CategoryTheory.ObjectProperty.Small.{w, v,…
· 使用定理 `CategoryTheory.Shrink.instLocallySmallShrink`：∀ (C : Type u) [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : Small.{w', u} C]   [CategoryTheory.Loca
llySmall.{w, v, u} C], CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.isEquivalence_ιOfLE_iff`：isEquivalence_ιOf
LE_iff : (ιOfLE h).IsEquivalence ↔ Q <= P.isoClosure
-/
lemma exists_equivalence_iff (P : ObjectProperty C) [LocallySmall.{w'} C] :
    (∃ (J : Type w) (_ : Category.{w'} J), Nonempty (P.FullSubcategory ≌ J)) ↔
      ObjectProperty.EssentiallySmall.{w} P := by
  refine ⟨fun ⟨J, _, ⟨e⟩⟩ ↦ ?_, fun _ ↦ ?_⟩
  · exact ⟨.ofObj (e.inverse ⋙ P.ι).obj, inferInstance,
      fun X hX ↦ ⟨_, ⟨⟨(e.functor.obj ⟨X, hX⟩)⟩, ⟨P.ι.mapIso (e.unitIso.app ⟨X, hX⟩)⟩⟩⟩⟩
  · obtain ⟨Q, _, h₁, h₂⟩ := EssentiallySmall.exists_small_le.{w} P
    rw [← isEquivalence_ιOfLE_iff h₁] at h₂
    exact ⟨_, _, ⟨((ιOfLE h₁).asEquivalence.symm.trans
      (Shrink.equivalence.{w} Q.FullSubcategory)).trans (ShrinkHoms.equivalence.{w'} _)⟩⟩

end ObjectProperty

variable {C D : Type*} [Category* C] [Category* D]

/-
**CategoryTheory.exists_equivalence_iff_of_locallySmall** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTh
eory.LocallySmall.{w', v_1, u_1} C],   (∃ J x, Nonempty (C ≌ J)) ↔ CategoryTheor
y.ObjectProperty.EssentiallySmall.{w, v_1, u_1} ⊤
参数：∃ J x, Nonempty (C ≌ J)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.exists_equivalence_iff`：exists_equivalence
_iff (P : ObjectProperty C) [LocallySmall.{w'} C] : (exists (J : Type w) (_ : Ca
tegory.{w'} J), Nonempty (P.FullSubcategor…
-/
lemma exists_equivalence_iff_of_locallySmall [LocallySmall.{w'} C] :
    (∃ (J : Type w) (_ : Category.{w'} J), Nonempty (C ≌ J)) ↔
      ObjectProperty.EssentiallySmall.{w} (C := C) ⊤ := by
  rw [← ObjectProperty.exists_equivalence_iff]
  exact ⟨fun ⟨J, _, ⟨e⟩⟩ ↦ ⟨J, _, ⟨(ObjectProperty.topEquivalence C).trans e⟩⟩,
    fun ⟨J, _, ⟨e⟩⟩ ↦ ⟨J, _, ⟨(ObjectProperty.topEquivalence C).symm.trans e⟩⟩⟩
/-
**CategoryTheory.essentiallySmall_iff_objectPropertyEssentiallySmall_top** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
ocallySmall.{w, v, u} C],   CategoryTheory.EssentiallySmall.{w, v, u} C ↔ Catego
ryTheory.ObjectProperty.EssentiallySmall.{w, v, u} ⊤
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.exists_equivalence_iff_of_locallySmall`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.LocallySmall.{w', 
v_1, u_1} C],   (∃ J x, Nonempty (C ≌ J)) ↔…
-/
lemma essentiallySmall_iff_objectPropertyEssentiallySmall_top
    (C : Type u) [Category.{v} C] [LocallySmall.{w} C] :
    EssentiallySmall.{w} C ↔ ObjectProperty.EssentiallySmall.{w} (C := C) ⊤ := by
  rw [← exists_equivalence_iff_of_locallySmall]
  exact ⟨fun _ ↦ ⟨_, _, ⟨equivSmallModel.{w} C⟩⟩,
    fun ⟨C₀, _, ⟨e⟩⟩ ↦ ⟨C₀, inferInstance, ⟨e⟩⟩⟩
/-
**CategoryTheory.essentiallySmall_iff_objectPropertyEssentiallySmall** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C],   Category
Theory.EssentiallySmall.{w, v_1, u_1} C ↔     CategoryTheory.LocallySmall.{w, v_
1, u_1} C ∧ CategoryTheory.ObjectProperty.EssentiallySmall.{w, v_1, u_1} ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `CategoryTheory.EssentiallySmall.equiv_smallCategory`：∀ {C : Type u} {ins
t : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.EssentiallySmall.{w
, v, u} C],   ∃ S x, Nonempty (C ≌ S)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma essentiallySmall_iff_objectPropertyEssentiallySmall :
    EssentiallySmall.{w} C ↔ LocallySmall.{w} C ∧
      ObjectProperty.EssentiallySmall.{w} (C := C) ⊤ := by
  wlog hC : LocallySmall.{w} C; · simp [essentiallySmall_iff, hC]
  simp only [hC, ← exists_equivalence_iff_of_locallySmall, true_and]
  refine ⟨fun H ↦ H.1, fun H ↦ ⟨H⟩⟩
/-
**CategoryTheory.EssentiallySmall.of_functor** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.EssentiallySmall`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : CategoryTheory.Functo
r C D)   [CategoryTheory.LocallySmall.{w, v_1, u_1} C],   CategoryTheory.ObjectP
roperty.EssentiallySmall.{w, v_2, u_2} F.essImage →     (∀ (Y : D), CategoryTheo
ry.ObjectProperty.EssentiallySmall.{w, v_1, u_1} fun x => Nonempty (F.obj x ≅ Y)
) →       CategoryTheory.EssentiallySmall.{w, v_1, u_1} C
参数：F : CategoryTheory.Functor C D；∀ (Y : D), CategoryTheory.ObjectProperty.Essen
tiallySmall.{w, v_1, u_1} fun x => Nonempty (F.obj x ≅ Y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.essentiallySmall_iff_objectPropertyEssentiallySmall`：∀ {C
 : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C],   CategoryTheory.Ess
entiallySmall.{w, v_1, u_1} C ↔     CategoryTheory.Local…
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.of_functor`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheo
ry.Category.{v', u'} D]   (P : CategoryTheory.O…
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.of_le`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.ObjectProperty C}  
 [CategoryTheory.ObjectProperty.Essentiall…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
-/
lemma EssentiallySmall.of_functor (F : C ⥤ D)
    [LocallySmall.{w} C] (H₁ : ObjectProperty.EssentiallySmall.{w} F.essImage)
    (H₂ : ∀ Y : D, ObjectProperty.EssentiallySmall.{w} (Nonempty <| F.obj · ≅ Y)) :
    EssentiallySmall.{w} C := by
  rw [essentiallySmall_iff_objectPropertyEssentiallySmall]
  exact ⟨‹_›, .of_functor _ F (.of_le (Q := F.essImage)
    fun Y ↦ by simp [ObjectProperty.map, Functor.essImage]) (by simpa)⟩

end CategoryTheory

