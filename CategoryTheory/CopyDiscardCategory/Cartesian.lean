/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
public import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Comon_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Cartesian Categories as Copy-Discard Categories

Every cartesian monoidal category is a copy-discard category where:
- Copy is the diagonal map
- Discard is the unique map to terminal

## Main results

* `CopyDiscardCategory` instance for cartesian monoidal categories
* All morphisms in cartesian categories are deterministic

## Tags

cartesian, copy-discard, comonoid, symmetric monoidal
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]

namespace CartesianCopyDiscard

/-- Provide `ComonObj` instances using the canonical cartesian comonoid structure. -/
/-
**CategoryTheory.CartesianCopyDiscard.instComonObjOfCartesian** 是 Mathlib 中的一个缩写
定义，位于命名空间 `CategoryTheory.CartesianCopyDiscard`。
形式化陈述：instComonObjOfCartesian (X : C) : ComonObj X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Provide `ComonObj` instances using the canonical cartesian comonoid structure.
-/
abbrev instComonObjOfCartesian (X : C) : ComonObj X :=
  ((cartesianComon C).obj X).comon

attribute [local instance] instComonObjOfCartesian

variable [BraidedCategory C]

/-- Every object in a cartesian category has commutative comonoid structure. -/
/-
**CategoryTheory.CartesianCopyDiscard.instIsCommComonObjOfCartesian** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.CartesianCopyDiscard`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory 
C] (X : C), CategoryTheory.IsCommComonObj X
参数：X : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.comul_eq_lift`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C] (A : C)   [
inst_2 : CategoryT…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_braiding_hom`：lift_braidin
g_hom {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ (β_ X Y).hom = lift g f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Every object in a cartesian category has commutative comonoid structure.
-/
instance instIsCommComonObjOfCartesian (X : C) : IsCommComonObj X where

/-- Cartesian categories have copy-discard structure. -/
/-
**CategoryTheory.CartesianCopyDiscard.ofCartesianMonoidalCategory** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.CartesianCopyDiscard`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] →       [CategoryTheory.BraidedCate
gory C] → CategoryTheory.CopyDiscardCategory C
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CartesianCopyDiscard.instIsCommComonObjOfCartesian`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Car
tesianMonoidalCategory C]   [inst_2 : CategoryTheory.Br…

--- 原说明 ---
Cartesian categories have copy-discard structure.
-/
abbrev ofCartesianMonoidalCategory : CopyDiscardCategory C where

attribute [local instance] ofCartesianMonoidalCategory

/-- In cartesian categories, every morphism is deterministic (preserves the comonoid structure). -/
/-
**CategoryTheory.CartesianCopyDiscard.instDeterministic** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.CartesianCopyDiscard`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory 
C] {X Y : C} (f : X ⟶ Y), CategoryTheory.Deterministic f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.counit_eq_toUnit`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C] (A : C) 
  [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.comp_toUnit`：comp_toUnit {X
 Y : C} (f : X ⟶ Y) : f ≫ toUnit Y = toUnit X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.comul_eq_lift`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C] (A : C)   [
inst_2 : CategoryT…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.comp_lift`：comp_lift {V W X Y :
 C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) : f ≫ lift g h = lift (f ≫ g) (f ≫ h)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_map`：lift_map {V W X Y Z :
 C} (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) : lift f g ≫ (h otimesₘ k) =
 lift (f ≫ h) (g ≫ k)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
In cartesian categories, every morphism is deterministic (preserves the comonoid
 structure).
-/
instance instDeterministic {X Y : C} (f : X ⟶ Y) : Deterministic f where

end CartesianCopyDiscard

end CategoryTheory

