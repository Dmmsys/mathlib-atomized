/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.PEmpty
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Initial and terminal objects in a category.

In this file we define the predicates `IsTerminal` and `IsInitial` as well as the class
`InitialMonoClass`.

The classes `HasTerminal` and `HasInitial` and the associated notations for terminal and initial
objects are defined in `Terminal.lean`.

## References
* [Stacks: Initial and final objects](https://stacks.math.columbia.edu/tag/002B)
-/

@[expose] public section

assert_not_exists CategoryTheory.Limits.HasLimit

noncomputable section

universe w w' v v₁ v₂ u u₁ u₂

open CategoryTheory Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
/-- Construct a cone for the empty diagram given an object. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Limits.asEmptyCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：asEmptyCone (X : C) : Cone (Functor.empty.{0} C)
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False

--- 原说明 ---
Construct a cone for the empty diagram given an object.
-/
def asEmptyCone (X : C) : Cone (Functor.empty.{0} C) :=
  { pt := X
    π :=
    { app := by cat_disch } }

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
/-- Construct a cocone for the empty diagram given an object. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Limits.asEmptyCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：asEmptyCocone (X : C) : Cocone (Functor.empty.{0} C)
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False

--- 原说明 ---
Construct a cocone for the empty diagram given an object.
-/
def asEmptyCocone (X : C) : Cocone (Functor.empty.{0} C) :=
  { pt := X
    ι :=
    { app := by cat_disch } }

/-- `X` is terminal if the cone it induces on the empty diagram is limiting. -/
/-
**CategoryTheory.Limits.IsTerminal** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：IsTerminal (X : C)
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X` is terminal if the cone it induces on the empty diagram is limiting.
-/
abbrev IsTerminal (X : C) :=
  IsLimit (asEmptyCone X)

/-- `X` is initial if the cocone it induces on the empty diagram is colimiting. -/
/-
**CategoryTheory.Limits.IsInitial** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：IsInitial (X : C)
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X` is initial if the cocone it induces on the empty diagram is colimiting.
-/
abbrev IsInitial (X : C) :=
  IsColimit (asEmptyCocone X)

/-- An object `Y` is terminal iff for every `X` there is a unique morphism `X ⟶ Y`. -/
/-
**CategoryTheory.Limits.isTerminalEquivUnique** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：isTerminalEquivUnique (F : Discrete.{0} PEmpty.{1} ⥤ C) (Y : C) : IsLimit 
(⟨Y, by cat_disch, by simp⟩ : Cone F) ≃ forall X : C, Unique (X ⟶ Y) where toFun
 t X
参数：F : Discrete.{0} PEmpty.{1} ⥤ C；Y : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False

--- 原说明 ---
An object `Y` is terminal iff for every `X` there is a unique morphism `X ⟶ Y`.
-/
def isTerminalEquivUnique (F : Discrete.{0} PEmpty.{1} ⥤ C) (Y : C) :
    IsLimit (⟨Y, by cat_disch, by simp⟩ : Cone F) ≃ ∀ X : C, Unique (X ⟶ Y) where
  toFun t X :=
    { default := t.lift ⟨X, ⟨by cat_disch, by simp⟩⟩
      uniq := fun f =>
        t.uniq ⟨X, ⟨by cat_disch, by simp⟩⟩ f (by simp) }
  invFun u :=
    { lift := fun s => (u s.pt).default
      uniq := fun s _ _ => (u s.pt).2 _ }
  left_inv := by dsimp [Function.LeftInverse]; intro x; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.RightInverse, Function.LeftInverse]
    subsingleton

/-- An object `Y` is terminal if for every `X` there is a unique morphism `X ⟶ Y`
    (as an instance). -/
/-
**CategoryTheory.Limits.IsTerminal.ofUnique** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.IsTerminal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (Y : C
) → [h : (X : C) → Unique (X ⟶ Y)] → CategoryTheory.Limits.IsTerminal Y
参数：Y : C；X : C；X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `Y` is terminal if for every `X` there is a unique morphism `X ⟶ Y`
    (as an instance).
-/
def IsTerminal.ofUnique (Y : C) [h : ∀ X : C, Unique (X ⟶ Y)] : IsTerminal Y where
  lift s := (h s.pt).default
  fac := fun _ ⟨j⟩ => j.elim

/-- An object `Y` is terminal if for every `X` there is a unique morphism `X ⟶ Y`
    (as explicit arguments). -/
/-
**CategoryTheory.Limits.IsTerminal.ofUniqueHom** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.IsTerminal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {Y : C
} → (h : (X : C) → X ⟶ Y) → (∀ (X : C) (m : X ⟶ Y), m = h X) → CategoryTheory.Li
mits.IsTerminal Y
参数：h : (X : C) → X ⟶ Y；∀ (X : C) (m : X ⟶ Y), m = h X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `Y` is terminal if for every `X` there is a unique morphism `X ⟶ Y`
    (as explicit arguments).
-/
def IsTerminal.ofUniqueHom {Y : C} (h : ∀ X : C, X ⟶ Y) (uniq : ∀ (X : C) (m : X ⟶ Y), m = h X) :
    IsTerminal Y :=
  have : ∀ X : C, Unique (X ⟶ Y) := fun X ↦ ⟨⟨h X⟩, uniq X⟩
  IsTerminal.ofUnique Y

/-- If `α` is a preorder with top, then `⊤` is a terminal object. -/
/-
**CategoryTheory.Limits.isTerminalTop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：isTerminalTop {α : Type*} [Preorder α] [OrderTop α] : IsTerminal (⊤ : α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is a preorder with top, then `⊤` is a terminal object.
-/
def isTerminalTop {α : Type*} [Preorder α] [OrderTop α] : IsTerminal (⊤ : α) :=
  IsTerminal.ofUnique _

/-- Transport a term of type `IsTerminal` across an isomorphism. -/
/-
**CategoryTheory.Limits.IsTerminal.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.IsTerminal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {Y Z :
 C} → CategoryTheory.Limits.IsTerminal Y → (Y ≅ Z) → CategoryTheory.Limits.IsTer
minal Z
参数：Y ≅ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a term of type `IsTerminal` across an isomorphism.
-/
def IsTerminal.ofIso {Y Z : C} (hY : IsTerminal Y) (i : Y ≅ Z) : IsTerminal Z :=
  IsLimit.ofIsoLimit hY
    { hom := { hom := i.hom }
      inv := { hom := i.inv } }

/-- If `X` and `Y` are isomorphic, then `X` is terminal iff `Y` is. -/
/-
**CategoryTheory.Limits.IsTerminal.equivOfIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.IsTerminal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → (X ≅ Y) → CategoryTheory.Limits.IsTerminal X ≃ CategoryTheory.Limits.IsTer
minal Y
参数：X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` and `Y` are isomorphic, then `X` is terminal iff `Y` is.
-/
def IsTerminal.equivOfIso {X Y : C} (e : X ≅ Y) :
    IsTerminal X ≃ IsTerminal Y where
  toFun h := IsTerminal.ofIso h e
  invFun h := IsTerminal.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- An object `X` is initial iff for every `Y` there is a unique morphism `X ⟶ Y`. -/
/-
**CategoryTheory.Limits.isInitialEquivUnique** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：isInitialEquivUnique (F : Discrete.{0} PEmpty.{1} ⥤ C) (X : C) : IsColimit
 (⟨X, ⟨by cat_disch, by simp⟩⟩ : Cocone F) ≃ forall Y : C, Unique (X ⟶ Y) where 
toFun t X
参数：F : Discrete.{0} PEmpty.{1} ⥤ C；X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False

--- 原说明 ---
An object `X` is initial iff for every `Y` there is a unique morphism `X ⟶ Y`.
-/
def isInitialEquivUnique (F : Discrete.{0} PEmpty.{1} ⥤ C) (X : C) :
    IsColimit (⟨X, ⟨by cat_disch, by simp⟩⟩ : Cocone F) ≃ ∀ Y : C, Unique (X ⟶ Y) where
  toFun t X :=
    { default := t.desc ⟨X, ⟨by cat_disch, by simp⟩⟩
      uniq := fun f => t.uniq ⟨X, ⟨by cat_disch, by simp⟩⟩ f (by simp) }
  invFun u :=
    { desc := fun s => (u s.pt).default
      uniq := fun s _ _ => (u s.pt).2 _ }
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by grind

/-- An object `X` is initial if for every `Y` there is a unique morphism `X ⟶ Y`
    (as an instance). -/
/-
**CategoryTheory.Limits.IsInitial.ofUnique** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.IsInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (X : C
) → [h : (Y : C) → Unique (X ⟶ Y)] → CategoryTheory.Limits.IsInitial X
参数：X : C；Y : C；X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` is initial if for every `Y` there is a unique morphism `X ⟶ Y`
    (as an instance).
-/
def IsInitial.ofUnique (X : C) [h : ∀ Y : C, Unique (X ⟶ Y)] : IsInitial X where
  desc s := (h s.pt).default
  fac := fun _ ⟨j⟩ => j.elim

/-- An object `X` is initial if for every `Y` there is a unique morphism `X ⟶ Y`
    (as explicit arguments). -/
/-
**CategoryTheory.Limits.IsInitial.ofUniqueHom** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.IsInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X : C
} → (h : (Y : C) → X ⟶ Y) → (∀ (Y : C) (m : X ⟶ Y), m = h Y) → CategoryTheory.Li
mits.IsInitial X
参数：h : (Y : C) → X ⟶ Y；∀ (Y : C) (m : X ⟶ Y), m = h Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` is initial if for every `Y` there is a unique morphism `X ⟶ Y`
    (as explicit arguments).
-/
def IsInitial.ofUniqueHom {X : C} (h : ∀ Y : C, X ⟶ Y) (uniq : ∀ (Y : C) (m : X ⟶ Y), m = h Y) :
    IsInitial X :=
  have : ∀ Y : C, Unique (X ⟶ Y) := fun Y ↦ ⟨⟨h Y⟩, uniq Y⟩
  IsInitial.ofUnique X

/-- If `α` is a preorder with bot, then `⊥` is an initial object. -/
/-
**CategoryTheory.Limits.isInitialBot** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：isInitialBot {α : Type*} [Preorder α] [OrderBot α] : IsInitial (⊥ : α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is a preorder with bot, then `⊥` is an initial object.
-/
def isInitialBot {α : Type*} [Preorder α] [OrderBot α] : IsInitial (⊥ : α) :=
  IsInitial.ofUnique _

/-- Transport a term of type `IsInitial` across an isomorphism. -/
/-
**CategoryTheory.Limits.IsInitial.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.IsInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → CategoryTheory.Limits.IsInitial X → (X ≅ Y) → CategoryTheory.Limits.IsInit
ial Y
参数：X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a term of type `IsInitial` across an isomorphism.
-/
def IsInitial.ofIso {X Y : C} (hX : IsInitial X) (i : X ≅ Y) : IsInitial Y :=
  IsColimit.ofIsoColimit hX
    { hom := { hom := i.hom }
      inv := { hom := i.inv } }

/-- If `X` and `Y` are isomorphic, then `X` is initial iff `Y` is. -/
/-
**CategoryTheory.Limits.IsInitial.equivOfIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.IsInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → (X ≅ Y) → CategoryTheory.Limits.IsInitial X ≃ CategoryTheory.Limits.IsInit
ial Y
参数：X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` and `Y` are isomorphic, then `X` is initial iff `Y` is.
-/
def IsInitial.equivOfIso {X Y : C} (e : X ≅ Y) :
    IsInitial X ≃ IsInitial Y where
  toFun h := IsInitial.ofIso h e
  invFun h := IsInitial.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Give the morphism to a terminal object from any other. -/
/-
**CategoryTheory.Limits.IsTerminal.from** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.IsTerminal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → {X : C} → 
CategoryTheory.Limits.IsTerminal X → (Y : C) → Y ⟶ X
参数：Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Give the morphism to a terminal object from any other.
-/
def IsTerminal.from {X : C} (t : IsTerminal X) (Y : C) : Y ⟶ X :=
  t.lift (asEmptyCone Y)

/-- Any two morphisms to a terminal object are equal. -/
/-
**CategoryTheory.Limits.IsTerminal.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.IsTerminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (t :
 CategoryTheory.Limits.IsTerminal X)   (f g : Y ⟶ X), f = g
参数：t : CategoryTheory.Limits.IsTerminal X；f g : Y ⟶ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)

--- 原说明 ---
Any two morphisms to a terminal object are equal.
-/
theorem IsTerminal.hom_ext {X Y : C} (t : IsTerminal X) (f g : Y ⟶ X) : f = g :=
  IsLimit.hom_ext t (by simp)

@[simp]
/-
**CategoryTheory.Limits.IsTerminal.comp_from** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.IsTerminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {Z : C} (t : C
ategoryTheory.Limits.IsTerminal Z) {X Y : C}   (f : X ⟶ Y), CategoryTheory.Categ
oryStruct.comp f (t.from Y) = t.from X
参数：t : CategoryTheory.Limits.IsTerminal Z；f : X ⟶ Y；t.from Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
-/
theorem IsTerminal.comp_from {Z : C} (t : IsTerminal Z) {X Y : C} (f : X ⟶ Y) :
    f ≫ t.from Y = t.from X :=
  t.hom_ext _ _

@[simp]
/-
**CategoryTheory.Limits.IsTerminal.from_self** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.IsTerminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (t : C
ategoryTheory.Limits.IsTerminal X),   t.from X = CategoryTheory.CategoryStruct.i
d X
参数：t : CategoryTheory.Limits.IsTerminal X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
-/
theorem IsTerminal.from_self {X : C} (t : IsTerminal X) : t.from X = 𝟙 X :=
  t.hom_ext _ _

/-- Give the morphism from an initial object to any other. -/
/-
**CategoryTheory.Limits.IsInitial.to** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.IsInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → {X : C} → 
CategoryTheory.Limits.IsInitial X → (Y : C) → X ⟶ Y
参数：Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Give the morphism from an initial object to any other.
-/
def IsInitial.to {X : C} (t : IsInitial X) (Y : C) : X ⟶ Y :=
  t.desc (asEmptyCocone Y)

/-- Any two morphisms from an initial object are equal. -/
/-
**CategoryTheory.Limits.IsInitial.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.IsInitial`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (t :
 CategoryTheory.Limits.IsInitial X)   (f g : X ⟶ Y), f = g
参数：t : CategoryTheory.Limits.IsInitial X；f g : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)

--- 原说明 ---
Any two morphisms from an initial object are equal.
-/
theorem IsInitial.hom_ext {X Y : C} (t : IsInitial X) (f g : X ⟶ Y) : f = g :=
  IsColimit.hom_ext t (by simp)

@[simp]
/-
**CategoryTheory.Limits.IsInitial.to_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.IsInitial`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (t : C
ategoryTheory.Limits.IsInitial X) {Y Z : C}   (f : Y ⟶ Z), CategoryTheory.Catego
ryStruct.comp (t.to Y) f = t.to Z
参数：t : CategoryTheory.Limits.IsInitial X；f : Y ⟶ Z；t.to Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
-/
theorem IsInitial.to_comp {X : C} (t : IsInitial X) {Y Z : C} (f : Y ⟶ Z) : t.to Y ≫ f = t.to Z :=
  t.hom_ext _ _

@[simp]
/-
**CategoryTheory.Limits.IsInitial.to_self** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.IsInitial`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (t : C
ategoryTheory.Limits.IsInitial X),   t.to X = CategoryTheory.CategoryStruct.id X
参数：t : CategoryTheory.Limits.IsInitial X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
-/
theorem IsInitial.to_self {X : C} (t : IsInitial X) : t.to X = 𝟙 X :=
  t.hom_ext _ _

/-- Any morphism from a terminal object is split mono. -/
/-
**CategoryTheory.Limits.IsTerminal.isSplitMono_from** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.IsTerminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (t :
 CategoryTheory.Limits.IsTerminal X)   (f : X ⟶ Y), CategoryTheory.IsSplitMono f
参数：t : CategoryTheory.Limits.IsTerminal X；f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitMono.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {X Y : C} {f : Y ⟶ X} (se : CategoryTheory.SplitMono f),   C
ategoryTheory.IsSpli…
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g

--- 原说明 ---
Any morphism from a terminal object is split mono.
-/
theorem IsTerminal.isSplitMono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : IsSplitMono f :=
  IsSplitMono.mk' ⟨t.from _, t.hom_ext _ _⟩

/-- Any morphism to an initial object is split epi. -/
/-
**CategoryTheory.Limits.IsInitial.isSplitEpi_to** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.IsInitial`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (t :
 CategoryTheory.Limits.IsInitial X)   (f : Y ⟶ X), CategoryTheory.IsSplitEpi f
参数：t : CategoryTheory.Limits.IsInitial X；f : Y ⟶ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitEpi.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (se : CategoryTheory.SplitEpi f),   Cat
egoryTheory.IsSplit…
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g

--- 原说明 ---
Any morphism to an initial object is split epi.
-/
theorem IsInitial.isSplitEpi_to {X Y : C} (t : IsInitial X) (f : Y ⟶ X) : IsSplitEpi f :=
  IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩

/-- Any morphism from a terminal object is mono. -/
/-
**CategoryTheory.Limits.IsTerminal.mono_from** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.IsTerminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (t :
 CategoryTheory.Limits.IsTerminal X)   (f : X ⟶ Y), CategoryTheory.Mono f
参数：t : CategoryTheory.Limits.IsTerminal X；f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.isSplitMono_from`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTe
rminal X)   (f : X ⟶ Y), CategoryTheory…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…

--- 原说明 ---
Any morphism from a terminal object is mono.
-/
theorem IsTerminal.mono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : Mono f := by
  have := t.isSplitMono_from f; infer_instance

/-- Any morphism to an initial object is epi. -/
/-
**CategoryTheory.Limits.IsInitial.epi_to** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.IsInitial`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (t :
 CategoryTheory.Limits.IsInitial X)   (f : Y ⟶ X), CategoryTheory.Epi f
参数：t : CategoryTheory.Limits.IsInitial X；f : Y ⟶ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.isSplitEpi_to`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitia
l X)   (f : Y ⟶ X), CategoryTheory.…
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f

--- 原说明 ---
Any morphism to an initial object is epi.
-/
theorem IsInitial.epi_to {X Y : C} (t : IsInitial X) (f : Y ⟶ X) : Epi f := by
  have := t.isSplitEpi_to f; infer_instance

/-- If `T` and `T'` are terminal, they are isomorphic. -/
@[simps]
/-
**CategoryTheory.Limits.IsTerminal.uniqueUpToIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.IsTerminal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {T T' 
: C} → CategoryTheory.Limits.IsTerminal T → CategoryTheory.Limits.IsTerminal T' 
→ (T ≅ T')
参数：T ≅ T'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `T` and `T'` are terminal, they are isomorphic.
-/
def IsTerminal.uniqueUpToIso {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') : T ≅ T' where
  hom := hT'.from _
  inv := hT.from _

/-- If `I` and `I'` are initial, they are isomorphic. -/
@[simps]
/-
**CategoryTheory.Limits.IsInitial.uniqueUpToIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.IsInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {I I' 
: C} → CategoryTheory.Limits.IsInitial I → CategoryTheory.Limits.IsInitial I' → 
(I ≅ I')
参数：I ≅ I'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `I` and `I'` are initial, they are isomorphic.
-/
def IsInitial.uniqueUpToIso {I I' : C} (hI : IsInitial I) (hI' : IsInitial I') : I ≅ I' where
  hom := hI.to _
  inv := hI'.to _

variable (C)

section Univ

variable (X : C) {F₁ : Discrete.{w} PEmpty ⥤ C} {F₂ : Discrete.{w'} PEmpty ⥤ C}

/-- Being terminal is independent of the empty diagram, its universe, and the cone over it,
    as long as the cone points are isomorphic. -/
/-
**CategoryTheory.Limits.isLimitChangeEmptyCone** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：isLimitChangeEmptyCone {c₁ : Cone F₁} (hl : IsLimit c₁) (c₂ : Cone F₂) (hi
 : c₁.pt ≅ c₂.pt) : IsLimit c₂ where lift c
参数：hl : IsLimit c₁；c₂ : Cone F₂；hi : c₁.pt ≅ c₂.pt。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False

--- 原说明 ---
Being terminal is independent of the empty diagram, its universe, and the cone o
ver it,
    as long as the cone points are isomorphic.
-/
def isLimitChangeEmptyCone {c₁ : Cone F₁} (hl : IsLimit c₁) (c₂ : Cone F₂) (hi : c₁.pt ≅ c₂.pt) :
    IsLimit c₂ where
  lift c := hl.lift ⟨c.pt, by cat_disch, by simp⟩ ≫ hi.hom
  uniq c f _ := by
    dsimp
    rw [← hl.uniq _ (f ≫ hi.inv) _]
    · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · simp

/-- Replacing an empty cone in `IsLimit` by another with the same cone point
    is an equivalence. -/
/-
**CategoryTheory.Limits.isLimitEmptyConeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：isLimitEmptyConeEquiv (c₁ : Cone F₁) (c₂ : Cone F₂) (h : c₁.pt ≅ c₂.pt) : 
IsLimit c₁ ≃ IsLimit c₂ where toFun hl
参数：c₁ : Cone F₁；c₂ : Cone F₂；h : c₁.pt ≅ c₂.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replacing an empty cone in `IsLimit` by another with the same cone point
    is an equivalence.
-/
def isLimitEmptyConeEquiv (c₁ : Cone F₁) (c₂ : Cone F₂) (h : c₁.pt ≅ c₂.pt) :
    IsLimit c₁ ≃ IsLimit c₂ where
  toFun hl := isLimitChangeEmptyCone C hl c₂ h
  invFun hl := isLimitChangeEmptyCone C hl c₁ h.symm
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.LeftInverse, Function.RightInverse]; intro
    simp only [eq_iff_true_of_subsingleton]

/-- If `F` is an empty diagram, then a cone over `F` is limiting iff the cone point is terminal. -/
noncomputable
/-
**CategoryTheory.Limits.isLimitEquivIsTerminalOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：isLimitEquivIsTerminalOfIsEmpty {J : Type*} [Category* J] [IsEmpty J] {F :
 J ⥤ C} (c : Cone F) : IsLimit c ≃ IsTerminal c.pt
参数：c : Cone F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)
-/
def isLimitEquivIsTerminalOfIsEmpty {J : Type*} [Category* J] [IsEmpty J] {F : J ⥤ C} (c : Cone F) :
    IsLimit c ≃ IsTerminal c.pt :=
  (IsLimit.whiskerEquivalenceEquiv (equivalenceOfIsEmpty (Discrete PEmpty.{1}) _)).trans
    (isLimitEmptyConeEquiv _ _ _ (.refl _))

/-- Being initial is independent of the empty diagram, its universe, and the cocone over it,
    as long as the cocone points are isomorphic. -/
/-
**CategoryTheory.Limits.isColimitChangeEmptyCocone** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：isColimitChangeEmptyCocone {c₁ : Cocone F₁} (hl : IsColimit c₁) (c₂ : Coco
ne F₂) (hi : c₁.pt ≅ c₂.pt) : IsColimit c₂ where desc c
参数：hl : IsColimit c₁；c₂ : Cocone F₂；hi : c₁.pt ≅ c₂.pt。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False

--- 原说明 ---
Being initial is independent of the empty diagram, its universe, and the cocone 
over it,
    as long as the cocone points are isomorphic.
-/
def isColimitChangeEmptyCocone {c₁ : Cocone F₁} (hl : IsColimit c₁) (c₂ : Cocone F₂)
    (hi : c₁.pt ≅ c₂.pt) : IsColimit c₂ where
  desc c := hi.inv ≫ hl.desc ⟨c.pt, by cat_disch, by simp⟩
  uniq c f _ := by
    dsimp
    rw [← hl.uniq _ (hi.hom ≫ f) _]
    · simp only [Iso.inv_hom_id_assoc]
    · simp

/-- Replacing an empty cocone in `IsColimit` by another with the same cocone point
    is an equivalence. -/
/-
**CategoryTheory.Limits.isColimitEmptyCoconeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：isColimitEmptyCoconeEquiv (c₁ : Cocone F₁) (c₂ : Cocone F₂) (h : c₁.pt ≅ c
₂.pt) : IsColimit c₁ ≃ IsColimit c₂ where toFun hl
参数：c₁ : Cocone F₁；c₂ : Cocone F₂；h : c₁.pt ≅ c₂.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replacing an empty cocone in `IsColimit` by another with the same cocone point
    is an equivalence.
-/
def isColimitEmptyCoconeEquiv (c₁ : Cocone F₁) (c₂ : Cocone F₂) (h : c₁.pt ≅ c₂.pt) :
    IsColimit c₁ ≃ IsColimit c₂ where
  toFun hl := isColimitChangeEmptyCocone C hl c₂ h
  invFun hl := isColimitChangeEmptyCocone C hl c₁ h.symm
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.LeftInverse, Function.RightInverse]; intro
    simp only [eq_iff_true_of_subsingleton]

/-- If `F` is an empty diagram,
then a cocone over `F` is colimiting iff the cocone point is initial. -/
noncomputable
/-
**CategoryTheory.Limits.isColimitEquivIsInitialOfIsEmpty** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：isColimitEquivIsInitialOfIsEmpty {J : Type*} [Category* J] [IsEmpty J] {F 
: J ⥤ C} (c : Cocone F) : IsColimit c ≃ IsInitial c.pt
参数：c : Cocone F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)
-/
def isColimitEquivIsInitialOfIsEmpty {J : Type*} [Category* J] [IsEmpty J]
    {F : J ⥤ C} (c : Cocone F) : IsColimit c ≃ IsInitial c.pt :=
  (IsColimit.whiskerEquivalenceEquiv (equivalenceOfIsEmpty (Discrete PEmpty.{1}) _)).trans
    (isColimitEmptyCoconeEquiv _ _ _ (.refl _))

end Univ

section

variable {C}

/-- An initial object is terminal in the opposite category. -/
/-
**CategoryTheory.Limits.terminalOpOfInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：terminalOpOfInitial {X : C} (t : IsInitial X) : IsTerminal (Opposite.op X)
 where lift s
参数：t : IsInitial X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An initial object is terminal in the opposite category.
-/
def terminalOpOfInitial {X : C} (t : IsInitial X) : IsTerminal (Opposite.op X) where
  lift s := (t.to s.pt.unop).op
  uniq _ _ _ := Quiver.Hom.unop_inj (t.hom_ext _ _)

/-- An initial object in the opposite category is terminal in the original category. -/
/-
**CategoryTheory.Limits.terminalUnopOfInitial** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：terminalUnopOfInitial {X : Cᵒᵖ} (t : IsInitial X) : IsTerminal X.unop wher
e lift s
参数：t : IsInitial X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An initial object in the opposite category is terminal in the original category.
-/
def terminalUnopOfInitial {X : Cᵒᵖ} (t : IsInitial X) : IsTerminal X.unop where
  lift s := (t.to (Opposite.op s.pt)).unop
  uniq _ _ _ := Quiver.Hom.op_inj (t.hom_ext _ _)

/-- A terminal object is initial in the opposite category. -/
/-
**CategoryTheory.Limits.initialOpOfTerminal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：initialOpOfTerminal {X : C} (t : IsTerminal X) : IsInitial (Opposite.op X)
 where desc s
参数：t : IsTerminal X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A terminal object is initial in the opposite category.
-/
def initialOpOfTerminal {X : C} (t : IsTerminal X) : IsInitial (Opposite.op X) where
  desc s := (t.from s.pt.unop).op
  uniq _ _ _ := Quiver.Hom.unop_inj (t.hom_ext _ _)

/-- A terminal object in the opposite category is initial in the original category. -/
/-
**CategoryTheory.Limits.initialUnopOfTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：initialUnopOfTerminal {X : Cᵒᵖ} (t : IsTerminal X) : IsInitial X.unop wher
e desc s
参数：t : IsTerminal X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A terminal object in the opposite category is initial in the original category.
-/
def initialUnopOfTerminal {X : Cᵒᵖ} (t : IsTerminal X) : IsInitial X.unop where
  desc s := (t.from (Opposite.op s.pt)).unop
  uniq _ _ _ := Quiver.Hom.op_inj (t.hom_ext _ _)

/-- A category is an `InitialMonoClass` if the canonical morphism of an initial object is a
monomorphism.  In practice, this is most useful when given an arbitrary morphism out of the chosen
initial object, see `initial.mono_from`.
Given a terminal object, this is equivalent to the assumption that the unique morphism from initial
to terminal is a monomorphism, which is the second of Freyd's axioms for an AT category.

TODO: This is a condition satisfied by categories with zero objects and morphisms.
-/
/-
**CategoryTheory.Limits.InitialMonoClass** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：(C : Type u₁) → [CategoryTheory.Category.{v₁, u₁} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is an `InitialMonoClass` if the canonical morphism of an initial obje
ct is a
monomorphism.  In practice, this is most useful when given an arbitrary morphism
 out of the chosen
initial object, see `initial.mono_from`.
Given a terminal object, this is equivalent to the assumption that the unique mo
rphism from initial
to terminal is a monomorphism, which is the second of Freyd's axioms for an AT c
ategory.

TODO: This is a condition satisfied by categories with zero objects and morphism
s.
-/
class InitialMonoClass (C : Type u₁) [Category.{v₁} C] : Prop where
  /-- The map from the (any as stated) initial object to any other object is a
    monomorphism -/
  isInitial_mono_from : ∀ {I} (X : C) (hI : IsInitial I), Mono (hI.to X)
/-
**CategoryTheory.Limits.IsInitial.mono_from** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.IsInitial`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.Limits.InitialMonoClass C] {I X : C}   (hI : CategoryTheory.Limits.IsInitial I
) (f : I ⟶ X), CategoryTheory.Mono f
参数：hI : CategoryTheory.Limits.IsInitial I；f : I ⟶ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
· 使用定理 `CategoryTheory.Limits.InitialMonoClass.isInitial_mono_from`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.Limits.In
itialMonoClass C] {I : C}   (X : C) (hI : Catego…
-/
theorem IsInitial.mono_from [InitialMonoClass C] {I} {X : C} (hI : IsInitial I) (f : I ⟶ X) :
    Mono f := by
  rw [hI.hom_ext f (hI.to X)]
  apply InitialMonoClass.isInitial_mono_from

/-- To show a category is an `InitialMonoClass` it suffices to give an initial object such that
every morphism out of it is a monomorphism. -/
/-
**CategoryTheory.Limits.InitialMonoClass.of_isInitial** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.InitialMonoClass`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {I : C} (hI : 
CategoryTheory.Limits.IsInitial I),   (∀ (X : C), CategoryTheory.Mono (hI.to X))
 → CategoryTheory.Limits.InitialMonoClass C
参数：hI : CategoryTheory.Limits.IsInitial I；∀ (X : C), CategoryTheory.Mono (hI.to 
X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
To show a category is an `InitialMonoClass` it suffices to give an initial objec
t such that
every morphism out of it is a monomorphism.
-/
theorem InitialMonoClass.of_isInitial {I : C} (hI : IsInitial I) (h : ∀ X, Mono (hI.to X)) :
    InitialMonoClass C where
  isInitial_mono_from {I'} X hI' := by
    rw [hI'.hom_ext (hI'.to X) ((hI'.uniqueUpToIso hI).hom ≫ hI.to X)]
    apply mono_comp

/-- To show a category is an `InitialMonoClass` it suffices to show the unique morphism from an
initial object to a terminal object is a monomorphism. -/
/-
**CategoryTheory.Limits.InitialMonoClass.of_isTerminal** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.InitialMonoClass`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {I T : C} (hI 
: CategoryTheory.Limits.IsInitial I)   (hT : CategoryTheory.Limits.IsTerminal T)
, CategoryTheory.Mono (hI.to T) → CategoryTheory.Limits.InitialMonoClass C
参数：hI : CategoryTheory.Limits.IsInitial I；hT : CategoryTheory.Limits.IsTerminal 
T；hI.to T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.InitialMonoClass.of_isInitial`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {I : C} (hI : CategoryTheory.Limits.IsI
nitial I),   (∀ (X : C), CategoryTheory.M…
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g

--- 原说明 ---
To show a category is an `InitialMonoClass` it suffices to show the unique morph
ism from an
initial object to a terminal object is a monomorphism.
-/
theorem InitialMonoClass.of_isTerminal {I T : C} (hI : IsInitial I) (hT : IsTerminal T)
    (_ : Mono (hI.to T)) : InitialMonoClass C :=
  InitialMonoClass.of_isInitial hI fun X => mono_of_mono_fac (hI.hom_ext (_ ≫ hT.from X) (hI.to T))

variable {J : Type u} [Category.{v} J]

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cone for `J`.
In `limitOfDiagramInitial` we show it is a limit cone. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Limits.coneOfDiagramInitial** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：coneOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) : Cone F where
 pt
参数：tX : IsInitial X；F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cone for
 `J`.
In `limitOfDiagramInitial` we show it is a limit cone.
-/
def coneOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) : Cone F where
  pt := F.obj X
  π :=
    { app := fun j => F.map (tX.to j)
      naturality := fun j j' k => by
        dsimp
        rw [← F.map_comp, Category.id_comp, tX.hom_ext (tX.to j ≫ k) (tX.to j')] }

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, show the cone
`coneOfDiagramInitial` is a limit. -/
/-
**CategoryTheory.Limits.limitOfDiagramInitial** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：limitOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) : IsLimit (co
neOfDiagramInitial tX F) where lift s
参数：tX : IsInitial X；F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a functor `F : J ⥤ C`, given an initial object of `J`, show the cone
`coneOfDiagramInitial` is a limit.
-/
def limitOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) :
    IsLimit (coneOfDiagramInitial tX F) where
  lift s := s.π.app X
  uniq s m w := by
    simp_rw [← w X, coneOfDiagramInitial_π_app, tX.hom_ext (tX.to X) (𝟙 _)]
    simp

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cone for `J`,
provided that the morphisms in the diagram are isomorphisms.
In `limitOfDiagramTerminal` we show it is a limit cone. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Limits.coneOfDiagramTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：coneOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C) [forall (i j
 : J) (f : i ⟶ j), IsIso (F.map f)] : Cone F where pt
参数：hX : IsTerminal X；F : J ⥤ C；i j : J；f : i ⟶ j；F.map f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cone for
 `J`,
provided that the morphisms in the diagram are isomorphisms.
In `limitOfDiagramTerminal` we show it is a limit cone.
-/
def coneOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : Cone F where
  pt := F.obj X
  π :=
    { app := fun _ => inv (F.map (hX.from _))
      naturality := by
        intro i j f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.id_comp, ← F.map_comp,
          hX.hom_ext (hX.from i) (f ≫ hX.from j)] }

/-- From a functor `F : J ⥤ C`, given a terminal object of `J` and that the morphisms in the
diagram are isomorphisms, show the cone `coneOfDiagramTerminal` is a limit. -/
/-
**CategoryTheory.Limits.limitOfDiagramTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：limitOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C) [forall (i 
j : J) (f : i ⟶ j), IsIso (F.map f)] : IsLimit (coneOfDiagramTerminal hX F) wher
e lift S
参数：hX : IsTerminal X；F : J ⥤ C；i j : J；f : i ⟶ j；F.map f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a functor `F : J ⥤ C`, given a terminal object of `J` and that the morphism
s in the
diagram are isomorphisms, show the cone `coneOfDiagramTerminal` is a limit.
-/
def limitOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsLimit (coneOfDiagramTerminal hX F) where
  lift S := S.π.app _

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cocone for `J`.
In `colimitOfDiagramTerminal` we show it is a colimit cocone. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Limits.coconeOfDiagramTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：coconeOfDiagramTerminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) : Cocone F
 where pt
参数：tX : IsTerminal X；F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cocone f
or `J`.
In `colimitOfDiagramTerminal` we show it is a colimit cocone.
-/
def coconeOfDiagramTerminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) : Cocone F where
  pt := F.obj X
  ι :=
    { app := fun j => F.map (tX.from j)
      naturality := fun j j' k => by
        dsimp
        rw [← F.map_comp, Category.comp_id, tX.hom_ext (k ≫ tX.from j') (tX.from j)] }

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, show the cocone
`coconeOfDiagramTerminal` is a colimit. -/
/-
**CategoryTheory.Limits.colimitOfDiagramTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：colimitOfDiagramTerminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) : IsColim
it (coconeOfDiagramTerminal tX F) where desc s
参数：tX : IsTerminal X；F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a functor `F : J ⥤ C`, given a terminal object of `J`, show the cocone
`coconeOfDiagramTerminal` is a colimit.
-/
def colimitOfDiagramTerminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) :
    IsColimit (coconeOfDiagramTerminal tX F) where
  desc s := s.ι.app X
  uniq s m w := by simp [← w X]
/-
**CategoryTheory.Limits.IsColimit.isIso_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsColimit.isIso_ι_app_of_isTerminal {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (X : J) (hX : IsTerminal X) :
    IsIso (c.ι.app X) := by
  change IsIso (coconePointUniqueUpToIso (colimitOfDiagramTerminal hX F) hc).hom
  infer_instance

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cocone for `J`,
provided that the morphisms in the diagram are isomorphisms.
In `colimitOfDiagramInitial` we show it is a colimit cocone. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Limits.coconeOfDiagramInitial** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：coconeOfDiagramInitial {X : J} (hX : IsInitial X) (F : J ⥤ C) [forall (i j
 : J) (f : i ⟶ j), IsIso (F.map f)] : Cocone F where pt
参数：hX : IsInitial X；F : J ⥤ C；i j : J；f : i ⟶ j；F.map f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cocone f
or `J`,
provided that the morphisms in the diagram are isomorphisms.
In `colimitOfDiagramInitial` we show it is a colimit cocone.
-/
def coconeOfDiagramInitial {X : J} (hX : IsInitial X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : Cocone F where
  pt := F.obj X
  ι :=
    { app := fun _ => inv (F.map (hX.to _))
      naturality := by
        intro i j f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.comp_id, ← F.map_comp,
          hX.hom_ext (hX.to i ≫ f) (hX.to j)] }

/-- From a functor `F : J ⥤ C`, given an initial object of `J` and that the morphisms in the
diagram are isomorphisms, show the cone `coconeOfDiagramInitial` is a colimit. -/
/-
**CategoryTheory.Limits.colimitOfDiagramInitial** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：colimitOfDiagramInitial {X : J} (hX : IsInitial X) (F : J ⥤ C) [forall (i 
j : J) (f : i ⟶ j), IsIso (F.map f)] : IsColimit (coconeOfDiagramInitial hX F) w
here desc S
参数：hX : IsInitial X；F : J ⥤ C；i j : J；f : i ⟶ j；F.map f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a functor `F : J ⥤ C`, given an initial object of `J` and that the morphism
s in the
diagram are isomorphisms, show the cone `coconeOfDiagramInitial` is a colimit.
-/
def colimitOfDiagramInitial {X : J} (hX : IsInitial X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsColimit (coconeOfDiagramInitial hX F) where
  desc S := S.ι.app _
/-
**CategoryTheory.Limits.IsLimit.isIso_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsLimit.isIso_π_app_of_isInitial {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
    (X : J) (hX : IsInitial X) :
    IsIso (c.π.app X) := by
  change IsIso (conePointUniqueUpToIso hc (limitOfDiagramInitial hX F)).hom
  infer_instance

/-- Any morphism between terminal objects is an isomorphism. -/
/-
**CategoryTheory.Limits.isIso_of_isTerminal** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：isIso_of_isTerminal {X Y : C} (hX : IsTerminal X) (hY : IsTerminal Y) (f :
 X ⟶ Y) : IsIso f
参数：hX : IsTerminal X；hY : IsTerminal Y；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsTerminal.comp_from`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {Z : C} (t : CategoryTheory.Limits.IsTerminal Z)
 {X Y : C}   (f : X ⟶ Y), Catego…
· 使用定理 `CategoryTheory.Limits.IsTerminal.from_self`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (t : CategoryTheory.Limits.IsTerminal X)
,   t.from X = CategoryTheory.Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g

--- 原说明 ---
Any morphism between terminal objects is an isomorphism.
-/
lemma isIso_of_isTerminal {X Y : C} (hX : IsTerminal X) (hY : IsTerminal Y) (f : X ⟶ Y) :
    IsIso f := by
  refine ⟨⟨IsTerminal.from hX Y, ?_⟩⟩
  simp only [IsTerminal.comp_from, IsTerminal.from_self, true_and]
  apply IsTerminal.hom_ext hY

/-- Any morphism between initial objects is an isomorphism. -/
/-
**CategoryTheory.Limits.isIso_of_isInitial** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：isIso_of_isInitial {X Y : C} (hX : IsInitial X) (hY : IsInitial Y) (f : X 
⟶ Y) : IsIso f
参数：hX : IsInitial X；hY : IsInitial Y；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.IsInitial.to_comp`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X : C} (t : CategoryTheory.Limits.IsInitial X) {Y 
Z : C}   (f : Y ⟶ Z), Categor…
· 使用定理 `CategoryTheory.Limits.IsInitial.to_self`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X : C} (t : CategoryTheory.Limits.IsInitial X),   
t.to X = CategoryTheory.Categ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g

--- 原说明 ---
Any morphism between initial objects is an isomorphism.
-/
lemma isIso_of_isInitial {X Y : C} (hX : IsInitial X) (hY : IsInitial Y) (f : X ⟶ Y) :
    IsIso f := by
  refine ⟨⟨IsInitial.to hY X, ?_⟩⟩
  simp only [IsInitial.to_comp, IsInitial.to_self, and_true]
  apply IsInitial.hom_ext hX

end

/-- An initial object is terminal in the opposite category. -/
/-
**CategoryTheory.Limits.IsInitial.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.IsInitial`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X : C
} → CategoryTheory.Limits.IsInitial X → CategoryTheory.Limits.IsTerminal (Opposi
te.op X)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An initial object is terminal in the opposite category.
-/
def IsInitial.op {X : C} (hX : IsInitial X) : IsTerminal (op X) :=
  IsTerminal.ofUniqueHom (fun _ ↦ (hX.to _).op)
    (fun _ _ ↦ Quiver.Hom.unop_inj (hX.hom_ext _ _))

/-- An initial object in the opposite category is terminal in the original category. -/
/-
**CategoryTheory.Limits.IsInitial.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.IsInitial`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X : C
ᵒᵖ} → CategoryTheory.Limits.IsInitial X → CategoryTheory.Limits.IsTerminal (Oppo
site.unop X)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An initial object in the opposite category is terminal in the original category.
-/
def IsInitial.unop {X : Cᵒᵖ} (hX : IsInitial X) : IsTerminal X.unop :=
  IsTerminal.ofUniqueHom (fun _ ↦ (hX.to _).unop)
    (fun _ _ ↦ Quiver.Hom.op_inj (hX.hom_ext _ _))

/-- A terminal object is initial in the opposite category. -/
/-
**CategoryTheory.Limits.IsTerminal.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.IsTerminal`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X : C
} → CategoryTheory.Limits.IsTerminal X → CategoryTheory.Limits.IsInitial (Opposi
te.op X)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A terminal object is initial in the opposite category.
-/
def IsTerminal.op {X : C} (hX : IsTerminal X) : IsInitial (op X) :=
  IsInitial.ofUniqueHom (fun _ ↦ (hX.from _).op)
    (fun _ _ ↦ Quiver.Hom.unop_inj (hX.hom_ext _ _))

/-- A terminal object in the opposite category is initial in the original category. -/
/-
**CategoryTheory.Limits.IsTerminal.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.IsTerminal`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X : C
ᵒᵖ} → CategoryTheory.Limits.IsTerminal X → CategoryTheory.Limits.IsInitial (Oppo
site.unop X)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A terminal object in the opposite category is initial in the original category.
-/
def IsTerminal.unop {X : Cᵒᵖ} (hX : IsTerminal X) : IsInitial X.unop :=
  IsInitial.ofUniqueHom (fun _ ↦ (hX.from _).unop)
    (fun _ _ ↦ Quiver.Hom.op_inj (hX.hom_ext _ _))

end Limits

namespace Functor
open Limits
variable (C : Type*) [Category* C] {D : Type*} [Category* D]

/-- The constant functor returning a specific terminal object is indeed terminal. -/
/-
**CategoryTheory.Functor.isTerminalConst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：(C : Type u_1) →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {X
 : D} →           CategoryTheory.Limits.IsTerminal X → CategoryTheory.Limits.IsT
erminal ((CategoryTheory.Functor.const C).obj X)
参数：CategoryTheory.Functor.const C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant functor returning a specific terminal object is indeed terminal.
-/
def isTerminalConst {X : D} (hX : IsTerminal X) :
    IsTerminal ((Functor.const C).obj X) :=
  .ofUniqueHom (fun Y => { app Z := hX.from (Y.obj Z) }) (by intros; ext; apply hX.hom_ext)

@[simp]
/-
**CategoryTheory.Functor.isTerminalConst_from_app** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {X : D} (hX : CategoryTheo
ry.Limits.IsTerminal X)   (F : CategoryTheory.Functor C D) (Y : C),   ((Category
Theory.Functor.isTerminalConst C hX).from F).app Y = hX.from (F.obj Y)
参数：C : Type u_1；hX : CategoryTheory.Limits.IsTerminal X；F : CategoryTheory.Funct
or C D；Y : C；(CategoryTheory.Functor.isTerminalConst C hX).from F；F.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isTerminalConst_from_app {X : D} (hX : IsTerminal X)
    (F : C ⥤ D) (Y : C) : ((isTerminalConst C hX).from F).app Y = hX.from (F.obj Y) := rfl

/-- The constant functor returning a specific initial object is indeed initial. -/
/-
**CategoryTheory.Functor.isInitialConst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：(C : Type u_1) →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {X
 : D} →           CategoryTheory.Limits.IsInitial X → CategoryTheory.Limits.IsIn
itial ((CategoryTheory.Functor.const C).obj X)
参数：CategoryTheory.Functor.const C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant functor returning a specific initial object is indeed initial.
-/
def isInitialConst {X : D} (hX : IsInitial X) :
    IsInitial ((Functor.const C).obj X) :=
  .ofUniqueHom (fun Y => { app Z := hX.to (Y.obj Z) }) (by intros; ext; apply hX.hom_ext)

@[simp]
/-
**CategoryTheory.Functor.isInitialConst_to_app** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {X : D} (hX : CategoryTheo
ry.Limits.IsInitial X)   (F : CategoryTheory.Functor C D) (Y : C), ((CategoryThe
ory.Functor.isInitialConst C hX).to F).app Y = hX.to (F.obj Y)
参数：C : Type u_1；hX : CategoryTheory.Limits.IsInitial X；F : CategoryTheory.Functo
r C D；Y : C；(CategoryTheory.Functor.isInitialConst C hX).to F；F.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isInitialConst_to_app {X : D} (hX : IsInitial X)
    (F : C ⥤ D) (Y : C) : ((isInitialConst C hX).to F).app Y = hX.to (F.obj Y) := rfl

end Functor

end CategoryTheory

