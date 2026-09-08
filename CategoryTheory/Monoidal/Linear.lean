/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Linear monoidal categories

A monoidal category is `MonoidalLinear R` if it is monoidal preadditive and
tensor product of morphisms is `R`-linear in both factors.
-/

public section


namespace CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

variable (R : Type*) [Semiring R]
variable (C : Type*) [Category* C] [Preadditive C] [Linear R C]
variable [MonoidalCategory C]

/-- A category is `MonoidalLinear R` if tensoring is `R`-linear in both factors.
-/
/-
**CategoryTheory.MonoidalLinear** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：MonoidalLinear [MonoidalPreadditive C] : Prop where whiskerLeft_smul : for
all (X : C) {Y Z : C} (r : R) (f : Y ⟶ Z), X ◁ (r • f) = r • (X ◁ f)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is `MonoidalLinear R` if tensoring is `R`-linear in both factors.
-/
class MonoidalLinear [MonoidalPreadditive C] : Prop where
  whiskerLeft_smul : ∀ (X : C) {Y Z : C} (r : R) (f : Y ⟶ Z), X ◁ (r • f) = r • (X ◁ f) := by
    cat_disch
  smul_whiskerRight : ∀ (r : R) {Y Z : C} (f : Y ⟶ Z) (X : C), (r • f) ▷ X = r • (f ▷ X) := by
    cat_disch

attribute [simp] MonoidalLinear.whiskerLeft_smul MonoidalLinear.smul_whiskerRight

variable {C}
variable [MonoidalPreadditive C] [MonoidalLinear R C]
/-
**CategoryTheory.tensorLeft_linear** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ (R : Type u_1) [inst : Semiring R] {C : Type u_2} [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C]   [inst_4 : CategoryTheory.MonoidalCategory C] [inst_5 
: CategoryTheory.MonoidalPreadditive C]   [CategoryTheory.MonoidalLinear R C] (X
 : C),   CategoryTheory.Functor.Linear R (CategoryTheory.MonoidalCategory.tensor
Left X)
参数：R : Type u_1；X : C；CategoryTheory.MonoidalCategory.tensorLeft X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalLinear.whiskerLeft_smul`：∀ {R : Type u_1} {inst :
 Semiring R} {C : Type u_2} {inst_1 : CategoryTheory.Category.{v_1, u_2} C}   {i
nst_2 : CategoryTheory.Preadditive C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance tensorLeft_linear (X : C) : (tensorLeft X).Linear R where
/-
**CategoryTheory.tensorRight_linear** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ (R : Type u_1) [inst : Semiring R] {C : Type u_2} [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C]   [inst_4 : CategoryTheory.MonoidalCategory C] [inst_5 
: CategoryTheory.MonoidalPreadditive C]   [CategoryTheory.MonoidalLinear R C] (X
 : C),   CategoryTheory.Functor.Linear R (CategoryTheory.MonoidalCategory.tensor
Right X)
参数：R : Type u_1；X : C；CategoryTheory.MonoidalCategory.tensorRight X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalLinear.smul_whiskerRight`：∀ {R : Type u_1} {inst 
: Semiring R} {C : Type u_2} {inst_1 : CategoryTheory.Category.{v_1, u_2} C}   {
inst_2 : CategoryTheory.Preadditive C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance tensorRight_linear (X : C) : (tensorRight X).Linear R where
/-
**CategoryTheory.tensoringLeft_linear** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：∀ (R : Type u_1) [inst : Semiring R] {C : Type u_2} [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C]   [inst_4 : CategoryTheory.MonoidalCategory C] [inst_5 
: CategoryTheory.MonoidalPreadditive C]   [CategoryTheory.MonoidalLinear R C] (X
 : C),   CategoryTheory.Functor.Linear R ((CategoryTheory.MonoidalCategory.tenso
ringLeft C).obj X)
参数：R : Type u_1；X : C；(CategoryTheory.MonoidalCategory.tensoringLeft C).obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalLinear.whiskerLeft_smul`：∀ {R : Type u_1} {inst :
 Semiring R} {C : Type u_2} {inst_1 : CategoryTheory.Category.{v_1, u_2} C}   {i
nst_2 : CategoryTheory.Preadditive C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance tensoringLeft_linear (X : C) : ((tensoringLeft C).obj X).Linear R where
/-
**CategoryTheory.tensoringRight_linear** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：∀ (R : Type u_1) [inst : Semiring R] {C : Type u_2} [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C]   [inst_4 : CategoryTheory.MonoidalCategory C] [inst_5 
: CategoryTheory.MonoidalPreadditive C]   [CategoryTheory.MonoidalLinear R C] (X
 : C),   CategoryTheory.Functor.Linear R ((CategoryTheory.MonoidalCategory.tenso
ringRight C).obj X)
参数：R : Type u_1；X : C；(CategoryTheory.MonoidalCategory.tensoringRight C).obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalLinear.smul_whiskerRight`：∀ {R : Type u_1} {inst 
: Semiring R} {C : Type u_2} {inst_1 : CategoryTheory.Category.{v_1, u_2} C}   {
inst_2 : CategoryTheory.Preadditive C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance tensoringRight_linear (X : C) : ((tensoringRight C).obj X).Linear R where

/-- A faithful linear monoidal functor to a linear monoidal category
ensures that the domain is linear monoidal. -/
/-
**CategoryTheory.MonoidalLinear.ofFaithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.MonoidalLinear`。
形式化陈述：∀ (R : Type u_1) [inst : Semiring R] {C : Type u_2} [inst_1 : CategoryTheo
ry.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C]   [inst_4 : CategoryTheory.MonoidalCategory C] [inst_5 
: CategoryTheory.MonoidalPreadditive C]   [CategoryTheory.MonoidalLinear R C] {D
 : Type u_3} [inst_7 : CategoryTheory.Category.{v_2, u_3} D]   [inst_8 : Categor
yTheory.Preadditive D] [inst_9 : CategoryTheory.Linear R D]   [inst_10 : Categor
yTheory.MonoidalCategory D] [inst_11 : CategoryTheory.MonoidalPreadditive D]   (
F : CategoryTheory.Functor D C) [F.Monoidal] [F.Faithful] [CategoryTheory.Functo
r.Linear R F],   CategoryTheory.MonoidalLinear R D
参数：R : Type u_1；F : CategoryTheory.Functor D C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.Monoidal.map_whiskerLeft`：map_whiskerLeft (X : C)
 {Y Z : C} (f : Y ⟶ Z) : F.map (X ◁ f) = δ F X Y ≫ F.obj X ◁ F.map f ≫ μ F X Z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_smul`：map_smul {X Y : C} (r : R) (f : X ⟶ Y) 
: F.map (r • f) = r • F.map f
· 使用定理 `CategoryTheory.MonoidalLinear.whiskerLeft_smul`：∀ {R : Type u_1} {inst :
 Semiring R} {C : Type u_2} {inst_1 : CategoryTheory.Category.{v_1, u_2} C}   {i
nst_2 : CategoryTheory.Preadditive C…
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.μ_natural_right`：∀ {C : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategor
y C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Linear.comp_smul`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.Monoidal.map_whiskerRight`：map_whiskerRight {X Y 
: C} (f : X ⟶ Y) (Z : C) : F.map (f ▷ Z) = δ F X Z ≫ F.map f ▷ F.obj Z ≫ μ F Y Z
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalLinear.smul_whiskerRight`：∀ {R : Type u_1} {inst 
: Semiring R} {C : Type u_2} {inst_1 : CategoryTheory.Category.{v_1, u_2} C}   {
inst_2 : CategoryTheory.Preadditive C…
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.μ_natural_left`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory
 C} {D : Type u₂}   {inst_2 : CategoryT…

--- 原说明 ---
A faithful linear monoidal functor to a linear monoidal category
ensures that the domain is linear monoidal.
-/
theorem MonoidalLinear.ofFaithful {D : Type*} [Category* D] [Preadditive D] [Linear R D]
    [MonoidalCategory D] [MonoidalPreadditive D] (F : D ⥤ C) [F.Monoidal] [F.Faithful]
    [F.Linear R] : MonoidalLinear R D :=
  { whiskerLeft_smul := by
      intro X Y Z r f
      apply F.map_injective
      rw [Functor.Monoidal.map_whiskerLeft]
      simp
    smul_whiskerRight := by
      intro r X Y f Z
      apply F.map_injective
      rw [Functor.Monoidal.map_whiskerRight]
      simp }

end CategoryTheory

