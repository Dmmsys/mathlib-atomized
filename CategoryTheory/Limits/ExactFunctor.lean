/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice

/-!
# Bundled exact functors

We say that a functor `F` is left exact if it preserves finite limits, it is right exact if it
preserves finite colimits, and it is exact if it is both left exact and right exact.

In this file, we define the categories of bundled left exact, right exact and exact functors.

-/

@[expose] public section


universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section

variable (C) (D)

/-- Left-exactness, as a property of objects in `C ⥤ D`. -/
/-
**CategoryTheory.leftExactFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：leftExactFunctor : ObjectProperty (C ⥤ D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left-exactness, as a property of objects in `C ⥤ D`.
-/
def leftExactFunctor : ObjectProperty (C ⥤ D) :=
  fun F ↦ PreservesFiniteLimits F

variable {C D} in
@[simp]
/-
**CategoryTheory.leftExactFunctor_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`
。
形式化陈述：leftExactFunctor_iff (F : C ⥤ D) : leftExactFunctor C D F ↔ PreservesFinit
eLimits F
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma leftExactFunctor_iff (F : C ⥤ D) :
    leftExactFunctor C D F ↔ PreservesFiniteLimits F := Iff.rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (leftExactFunctor C D).IsClosedUnderIsomorphisms where
  of_iso e h := by
    simp only [leftExactFunctor_iff] at h ⊢
    exact preservesFiniteLimits_of_natIso e

/-- Bundled left-exact functors. -/
/-
**CategoryTheory.LeftExactFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：LeftExactFunctor
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled left-exact functors.
-/
abbrev LeftExactFunctor := (leftExactFunctor C D).FullSubcategory

/-- `C ⥤ₗ D` denotes left exact functors `C ⥤ D` -/
infixr:26 " ⥤ₗ " => LeftExactFunctor

/-- A left exact functor is in particular a functor. -/
/-
**CategoryTheory.LeftExactFunctor.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.LeftExactFunctor`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (D : T
ype u₂) →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor (C ⥤ₗ D) (CategoryTheory.Functor C D)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left exact functor is in particular a functor.
-/
abbrev LeftExactFunctor.forget : (C ⥤ₗ D) ⥤ C ⥤ D :=
  ObjectProperty.ι _

/-- The inclusion of left exact functors into functors is fully faithful. -/
/-
**CategoryTheory.LeftExactFunctor.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.LeftExactFunctor`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (D : T
ype u₂) →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → (CategoryTheory.
LeftExactFunctor.forget C D).FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of left exact functors into functors is fully faithful.
-/
abbrev LeftExactFunctor.fullyFaithful : (LeftExactFunctor.forget C D).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/-- Right-exactness, as a property of objects in `C ⥤ D`. -/
/-
**CategoryTheory.rightExactFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：rightExactFunctor : ObjectProperty (C ⥤ D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right-exactness, as a property of objects in `C ⥤ D`.
-/
def rightExactFunctor : ObjectProperty (C ⥤ D) :=
  fun F ↦ PreservesFiniteColimits F

variable {C D} in
@[simp]
/-
**CategoryTheory.rightExactFunctor_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
`。
形式化陈述：rightExactFunctor_iff (F : C ⥤ D) : rightExactFunctor C D F ↔ PreservesFin
iteColimits F
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rightExactFunctor_iff (F : C ⥤ D) :
    rightExactFunctor C D F ↔ PreservesFiniteColimits F := Iff.rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (rightExactFunctor C D).IsClosedUnderIsomorphisms where
  of_iso e h := by
    simp only [rightExactFunctor_iff] at h ⊢
    exact preservesFiniteColimits_of_natIso e

/-- Bundled right-exact functors. -/
/-
**CategoryTheory.RightExactFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：RightExactFunctor
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled right-exact functors.
-/
abbrev RightExactFunctor := (rightExactFunctor C D).FullSubcategory

/-- `C ⥤ᵣ D` denotes right exact functors `C ⥤ D` -/
infixr:26 " ⥤ᵣ " => RightExactFunctor

/-- A right exact functor is in particular a functor. -/
/-
**CategoryTheory.RightExactFunctor.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.RightExactFunctor`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (D : T
ype u₂) →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor (C ⥤ᵣ D) (CategoryTheory.Functor C D)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A right exact functor is in particular a functor.
-/
abbrev RightExactFunctor.forget : (C ⥤ᵣ D) ⥤ C ⥤ D :=
  ObjectProperty.ι _

/-- The inclusion of right exact functors into functors is fully faithful. -/
/-
**CategoryTheory.RightExactFunctor.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.RightExactFunctor`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (D : T
ype u₂) →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → (CategoryTheory.
RightExactFunctor.forget C D).FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of right exact functors into functors is fully faithful.
-/
abbrev RightExactFunctor.fullyFaithful : (RightExactFunctor.forget C D).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/-- Exactness, as a property of objects in `C ⥤ D`. -/
/-
**CategoryTheory.exactFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：exactFunctor : ObjectProperty (C ⥤ D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exactness, as a property of objects in `C ⥤ D`.
-/
def exactFunctor : ObjectProperty (C ⥤ D) :=
  leftExactFunctor C D ⊓ rightExactFunctor C D

variable {C D} in
@[simp]
/-
**CategoryTheory.exactFunctor_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：exactFunctor_iff (F : C ⥤ D) : exactFunctor C D F ↔ PreservesFiniteLimits 
F ∧ PreservesFiniteColimits F
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma exactFunctor_iff (F : C ⥤ D) :
    exactFunctor C D F ↔ PreservesFiniteLimits F ∧ PreservesFiniteColimits F := Iff.rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (exactFunctor C D).IsClosedUnderIsomorphisms := by
  dsimp [exactFunctor]
  infer_instance

/-- Bundled exact functors. -/
/-
**CategoryTheory.ExactFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：ExactFunctor
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled exact functors.
-/
abbrev ExactFunctor := (exactFunctor C D).FullSubcategory

/-- `C ⥤ₑ D` denotes exact functors `C ⥤ D` -/
infixr:26 " ⥤ₑ " => ExactFunctor

/-- An exact functor is in particular a functor. -/
/-
**CategoryTheory.ExactFunctor.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.E
xactFunctor`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (D : T
ype u₂) →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor (C ⥤ₑ D) (CategoryTheory.Functor C D)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An exact functor is in particular a functor.
-/
abbrev ExactFunctor.forget : (C ⥤ₑ D) ⥤ C ⥤ D :=
  ObjectProperty.ι _
/-
**CategoryTheory.exactFunctor_le_leftExactFunctor** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：exactFunctor_le_leftExactFunctor : exactFunctor C D <= leftExactFunctor C 
D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma exactFunctor_le_leftExactFunctor :
    exactFunctor C D ≤ leftExactFunctor C D :=
  fun _ h ↦ h.1
/-
**CategoryTheory.exactFunctor_le_rightExactFunctor** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：exactFunctor_le_rightExactFunctor : exactFunctor C D <= rightExactFunctor 
C D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma exactFunctor_le_rightExactFunctor :
    exactFunctor C D ≤ rightExactFunctor C D :=
  fun _ h ↦ h.2

/-- Turn an exact functor into a left exact functor. -/
/-
**CategoryTheory.LeftExactFunctor.ofExact** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.LeftExactFunctor`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (D : T
ype u₂) → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 (C ⥤ₑ D) (C ⥤ₗ D)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.exactFunctor_le_leftExactFunctor`：exactFunctor_le_leftExa
ctFunctor : exactFunctor C D <= leftExactFunctor C D

--- 原说明 ---
Turn an exact functor into a left exact functor.
-/
abbrev LeftExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ₗ D :=
  ObjectProperty.ιOfLE (exactFunctor_le_leftExactFunctor C D)

/-- Turn an exact functor into a left exact functor. -/
/-
**CategoryTheory.RightExactFunctor.ofExact** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.RightExactFunctor`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (D : T
ype u₂) → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 (C ⥤ₑ D) (C ⥤ᵣ D)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.exactFunctor_le_rightExactFunctor`：exactFunctor_le_rightE
xactFunctor : exactFunctor C D <= rightExactFunctor C D

--- 原说明 ---
Turn an exact functor into a left exact functor.
-/
abbrev RightExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ᵣ D :=
  ObjectProperty.ιOfLE (exactFunctor_le_rightExactFunctor C D)

variable {C D}

@[simp]
/-
**CategoryTheory.LeftExactFunctor.ofExact_obj** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.LeftExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : C ⥤ₑ D), (CategoryTheory.Le
ftExactFunctor.ofExact C D).obj F = { obj := F.obj, property := ⋯ }
参数：F : C ⥤ₑ D；CategoryTheory.LeftExactFunctor.ofExact C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LeftExactFunctor.ofExact_obj (F : C ⥤ₑ D) :
    (LeftExactFunctor.ofExact C D).obj F = ⟨F.1, F.2.1⟩ :=
  rfl

@[simp]
/-
**CategoryTheory.RightExactFunctor.ofExact_obj** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.RightExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : C ⥤ₑ D), (CategoryTheory.Ri
ghtExactFunctor.ofExact C D).obj F = { obj := F.obj, property := ⋯ }
参数：F : C ⥤ₑ D；CategoryTheory.RightExactFunctor.ofExact C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RightExactFunctor.ofExact_obj (F : C ⥤ₑ D) :
    (RightExactFunctor.ofExact C D).obj F = ⟨F.1, F.2.2⟩ :=
  rfl

@[simp]
/-
**CategoryTheory.LeftExactFunctor.ofExact_map_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.LeftExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : C ⥤ₑ D} (α : F ⟶ G), ((Ca
tegoryTheory.LeftExactFunctor.ofExact C D).map α).hom = α.hom
参数：α : F ⟶ G；(CategoryTheory.LeftExactFunctor.ofExact C D).map α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LeftExactFunctor.ofExact_map_hom {F G : C ⥤ₑ D} (α : F ⟶ G) :
    ((LeftExactFunctor.ofExact C D).map α).hom = α.hom :=
  rfl

@[simp]
/-
**CategoryTheory.RightExactFunctor.ofExact_map_hom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.RightExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : C ⥤ₑ D} (α : F ⟶ G), ((Ca
tegoryTheory.RightExactFunctor.ofExact C D).map α).hom = α.hom
参数：α : F ⟶ G；(CategoryTheory.RightExactFunctor.ofExact C D).map α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RightExactFunctor.ofExact_map_hom {F G : C ⥤ₑ D} (α : F ⟶ G) :
    ((RightExactFunctor.ofExact C D).map α).hom = α.hom :=
  rfl

@[simp]
/-
**CategoryTheory.LeftExactFunctor.forget_obj** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.LeftExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : C ⥤ₗ D), (CategoryTheory.Le
ftExactFunctor.forget C D).obj F = F.obj
参数：F : C ⥤ₗ D；CategoryTheory.LeftExactFunctor.forget C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LeftExactFunctor.forget_obj (F : C ⥤ₗ D) : (LeftExactFunctor.forget C D).obj F = F.1 :=
  rfl

@[simp]
/-
**CategoryTheory.RightExactFunctor.forget_obj** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.RightExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : C ⥤ᵣ D), (CategoryTheory.Ri
ghtExactFunctor.forget C D).obj F = F.obj
参数：F : C ⥤ᵣ D；CategoryTheory.RightExactFunctor.forget C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RightExactFunctor.forget_obj (F : C ⥤ᵣ D) : (RightExactFunctor.forget C D).obj F = F.1 :=
  rfl

@[simp]
/-
**CategoryTheory.ExactFunctor.forget_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.ExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : C ⥤ₑ D), (CategoryTheory.Ex
actFunctor.forget C D).obj F = F.obj
参数：F : C ⥤ₑ D；CategoryTheory.ExactFunctor.forget C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ExactFunctor.forget_obj (F : C ⥤ₑ D) : (ExactFunctor.forget C D).obj F = F.1 :=
  rfl

@[simp]
/-
**CategoryTheory.LeftExactFunctor.forget_map** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.LeftExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : C ⥤ₗ D} (α : F ⟶ G), (Cat
egoryTheory.LeftExactFunctor.forget C D).map α = α.hom
参数：α : F ⟶ G；CategoryTheory.LeftExactFunctor.forget C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LeftExactFunctor.forget_map {F G : C ⥤ₗ D} (α : F ⟶ G) :
    (LeftExactFunctor.forget C D).map α = α.hom :=
  rfl

@[simp]
/-
**CategoryTheory.RightExactFunctor.forget_map** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.RightExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : C ⥤ᵣ D} (α : F ⟶ G), (Cat
egoryTheory.RightExactFunctor.forget C D).map α = α.hom
参数：α : F ⟶ G；CategoryTheory.RightExactFunctor.forget C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RightExactFunctor.forget_map {F G : C ⥤ᵣ D} (α : F ⟶ G) :
    (RightExactFunctor.forget C D).map α = α.hom :=
  rfl

@[simp]
/-
**CategoryTheory.ExactFunctor.forget_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.ExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : C ⥤ₑ D} (α : F ⟶ G), (Cat
egoryTheory.ExactFunctor.forget C D).map α = α.hom
参数：α : F ⟶ G；CategoryTheory.ExactFunctor.forget C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ExactFunctor.forget_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (ExactFunctor.forget C D).map α = α.hom :=
  rfl

/-- Turn a left exact functor into an object of the category `LeftExactFunctor C D`. -/
/-
**CategoryTheory.LeftExactFunctor.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
eftExactFunctor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor C D) → [CategoryTheory.Limits.PreservesFiniteLimits F] → C ⥤
ₗ D
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a left exact functor into an object of the category `LeftExactFunctor C D`.
-/
def LeftExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] : C ⥤ₗ D :=
  ⟨F, by simpa⟩

/-- Turn a right exact functor into an object of the category `RightExactFunctor C D`. -/
/-
**CategoryTheory.RightExactFunctor.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
RightExactFunctor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor C D) → [CategoryTheory.Limits.PreservesFiniteColimits F] → C
 ⥤ᵣ D
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a right exact functor into an object of the category `RightExactFunctor C D
`.
-/
def RightExactFunctor.of (F : C ⥤ D) [PreservesFiniteColimits F] : C ⥤ᵣ D :=
  ⟨F, by simpa⟩

/-- Turn an exact functor into an object of the category `ExactFunctor C D`. -/
/-
**CategoryTheory.ExactFunctor.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Exact
Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor C D) →           [CategoryTheory.Limits.PreservesFiniteLimit
s F] → [CategoryTheory.Limits.PreservesFiniteColimits F] → C ⥤ₑ D
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn an exact functor into an object of the category `ExactFunctor C D`.
-/
def ExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] : C ⥤ₑ D :=
  ⟨F, by simp only [exactFunctor_iff]; constructor <;> assumption⟩

@[simp]
/-
**CategoryTheory.LeftExactFunctor.of_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.LeftExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [inst_2 : CategoryTheory.Limits.PreservesFiniteLimits F],   (CategoryTheory.Lef
tExactFunctor.of F).obj = F
参数：F : CategoryTheory.Functor C D；CategoryTheory.LeftExactFunctor.of F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LeftExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] :
    (LeftExactFunctor.of F).obj = F :=
  rfl

@[simp]
/-
**CategoryTheory.RightExactFunctor.of_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.RightExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [inst_2 : CategoryTheory.Limits.PreservesFiniteColimits F],   (CategoryTheory.R
ightExactFunctor.of F).obj = F
参数：F : CategoryTheory.Functor C D；CategoryTheory.RightExactFunctor.of F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RightExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteColimits F] :
    (RightExactFunctor.of F).obj = F :=
  rfl

@[simp]
/-
**CategoryTheory.ExactFunctor.of_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.E
xactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [inst_2 : CategoryTheory.Limits.PreservesFiniteLimits F]   [inst_3 : CategoryTh
eory.Limits.PreservesFiniteColimits F], (CategoryTheory.ExactFunctor.of F).obj =
 F
参数：F : CategoryTheory.Functor C D；CategoryTheory.ExactFunctor.of F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (ExactFunctor.of F).obj = F :=
  rfl
/-
**CategoryTheory.LeftExactFunctor.forget_obj_of** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.LeftExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [inst_2 : CategoryTheory.Limits.PreservesFiniteLimits F],   (CategoryTheory.Lef
tExactFunctor.forget C D).obj (CategoryTheory.LeftExactFunctor.of F) = F
参数：F : CategoryTheory.Functor C D；CategoryTheory.LeftExactFunctor.forget C D；Cat
egoryTheory.LeftExactFunctor.of F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LeftExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F] :
    (LeftExactFunctor.forget C D).obj (LeftExactFunctor.of F) = F :=
  rfl
/-
**CategoryTheory.RightExactFunctor.forget_obj_of** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.RightExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [inst_2 : CategoryTheory.Limits.PreservesFiniteColimits F],   (CategoryTheory.R
ightExactFunctor.forget C D).obj (CategoryTheory.RightExactFunctor.of F) = F
参数：F : CategoryTheory.Functor C D；CategoryTheory.RightExactFunctor.forget C D；Ca
tegoryTheory.RightExactFunctor.of F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RightExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteColimits F] :
    (RightExactFunctor.forget C D).obj (RightExactFunctor.of F) = F :=
  rfl
/-
**CategoryTheory.ExactFunctor.forget_obj_of** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.ExactFunctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [inst_2 : CategoryTheory.Limits.PreservesFiniteLimits F]   [inst_3 : CategoryTh
eory.Limits.PreservesFiniteColimits F],   (CategoryTheory.ExactFunctor.forget C 
D).obj (CategoryTheory.ExactFunctor.of F) = F
参数：F : CategoryTheory.Functor C D；CategoryTheory.ExactFunctor.forget C D；Categor
yTheory.ExactFunctor.of F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : (ExactFunctor.forget C D).obj (ExactFunctor.of F) = F :=
  rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (F : C ⥤ₗ D) : PreservesFiniteLimits F.obj :=
  F.property
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (F : C ⥤ᵣ D) : PreservesFiniteColimits F.obj :=
  F.property
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (F : C ⥤ₑ D) : PreservesFiniteLimits F.obj :=
  F.property.1
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (F : C ⥤ₑ D) : PreservesFiniteColimits F.obj :=
  F.property.2

variable {E : Type u₃} [Category.{v₃} E]

section

variable (C D E)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering a left exact functor by a left exact functor yields a left exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
/-
**CategoryTheory.LeftExactFunctor.whiskeringLeft** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.LeftExactFunctor`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (D : T
ype u₂) →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (E : Typ
e u₃) →           [inst_2 : CategoryTheory.Category.{v₃, u₃} E] →             Ca
tegoryTheory.Functor (C ⥤ₗ D) (CategoryTheory.Functor (D ⥤ₗ E) (C ⥤ₗ E))
参数：D ⥤ₗ E；C ⥤ₗ E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering a left exact functor by a left exact functor yields a left exact func
tor.
-/
def LeftExactFunctor.whiskeringLeft : (C ⥤ₗ D) ⥤ (D ⥤ₗ E) ⥤ (C ⥤ₗ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteLimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering a left exact functor by a left exact functor yields a left exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
/-
**CategoryTheory.LeftExactFunctor.whiskeringRight** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.LeftExactFunctor`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (D : T
ype u₂) →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (E : Typ
e u₃) →           [inst_2 : CategoryTheory.Category.{v₃, u₃} E] →             Ca
tegoryTheory.Functor (D ⥤ₗ E) (CategoryTheory.Functor (C ⥤ₗ D) (C ⥤ₗ E))
参数：C ⥤ₗ D；C ⥤ₗ E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering a left exact functor by a left exact functor yields a left exact func
tor.
-/
def LeftExactFunctor.whiskeringRight : (D ⥤ₗ E) ⥤ (C ⥤ₗ D) ⥤ (C ⥤ₗ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteLimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering a right exact functor by a right exact functor yields a right exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
/-
**CategoryTheory.RightExactFunctor.whiskeringLeft** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.RightExactFunctor`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (D : T
ype u₂) →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (E : Typ
e u₃) →           [inst_2 : CategoryTheory.Category.{v₃, u₃} E] →             Ca
tegoryTheory.Functor (C ⥤ᵣ D) (CategoryTheory.Functor (D ⥤ᵣ E) (C ⥤ᵣ E))
参数：D ⥤ᵣ E；C ⥤ᵣ E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering a right exact functor by a right exact functor yields a right exact f
unctor.
-/
def RightExactFunctor.whiskeringLeft : (C ⥤ᵣ D) ⥤ (D ⥤ᵣ E) ⥤ (C ⥤ᵣ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteColimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering a right exact functor by a right exact functor yields a right exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
/-
**CategoryTheory.RightExactFunctor.whiskeringRight** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.RightExactFunctor`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (D : T
ype u₂) →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (E : Typ
e u₃) →           [inst_2 : CategoryTheory.Category.{v₃, u₃} E] →             Ca
tegoryTheory.Functor (D ⥤ᵣ E) (CategoryTheory.Functor (C ⥤ᵣ D) (C ⥤ᵣ E))
参数：C ⥤ᵣ D；C ⥤ᵣ E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering a right exact functor by a right exact functor yields a right exact f
unctor.
-/
def RightExactFunctor.whiskeringRight : (D ⥤ᵣ E) ⥤ (C ⥤ᵣ D) ⥤ (C ⥤ᵣ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteColimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering an exact functor by an exact functor yields an exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
/-
**CategoryTheory.ExactFunctor.whiskeringLeft** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ExactFunctor`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (D : T
ype u₂) →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (E : Typ
e u₃) →           [inst_2 : CategoryTheory.Category.{v₃, u₃} E] →             Ca
tegoryTheory.Functor (C ⥤ₑ D) (CategoryTheory.Functor (D ⥤ₑ E) (C ⥤ₑ E))
参数：D ⥤ₑ E；C ⥤ₑ E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering an exact functor by an exact functor yields an exact functor.
-/
def ExactFunctor.whiskeringLeft : (C ⥤ₑ D) ⥤ (D ⥤ₑ E) ⥤ (C ⥤ₑ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => ⟨by dsimp; exact comp_preservesFiniteLimits _ _,
      by dsimp; exact comp_preservesFiniteColimits _ _⟩)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering an exact functor by an exact functor yields an exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
/-
**CategoryTheory.ExactFunctor.whiskeringRight** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ExactFunctor`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (D : T
ype u₂) →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (E : Typ
e u₃) →           [inst_2 : CategoryTheory.Category.{v₃, u₃} E] →             Ca
tegoryTheory.Functor (D ⥤ₑ E) (CategoryTheory.Functor (C ⥤ₑ D) (C ⥤ₑ E))
参数：C ⥤ₑ D；C ⥤ₑ E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering an exact functor by an exact functor yields an exact functor.
-/
def ExactFunctor.whiskeringRight : (D ⥤ₑ E) ⥤ (C ⥤ₑ D) ⥤ (C ⥤ₑ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => ⟨by dsimp; exact comp_preservesFiniteLimits _ _,
      by dsimp; exact comp_preservesFiniteColimits _ _⟩)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

end

end

end CategoryTheory

