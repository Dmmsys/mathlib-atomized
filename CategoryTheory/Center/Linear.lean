/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Center.Preadditive

/-!
# Center of a linear category

If `C` is an `R`-linear category, we define a ring morphism `R →+* CatCenter C`
and conversely, if `C` is a preadditive category, and `φ : R →+* CatCenter C`
is a ring morphism, we define an `R`-linear structure on `C` attached to `φ`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits

namespace Linear

variable (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Preadditive C]

open scoped IsMulCommutative in
/-- The canonical morphism `R →+* CatCenter C` when `C` is an `R`-linear category. -/
@[simps]
/-
**CategoryTheory.Linear.toCatCenter** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
near`。
形式化陈述：toCatCenter [Linear R C] : R ->+* CatCenter C where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `R →+* CatCenter C` when `C` is an `R`-linear category.
-/
def toCatCenter [Linear R C] : R →+* CatCenter C where
  toFun a :=
    { app := fun X => a • 𝟙 X }
  map_one' := by cat_disch
  map_mul' a b := by
    rw [mul_comm]
    ext X
    dsimp only [CatCenter.mul_app']
    rw [Linear.smul_comp, Linear.comp_smul, smul_smul]
    simp
  map_zero' := by cat_disch
  map_add' a b := by ext X; simp [add_smul]

section

variable {R C}
variable (φ : R →+* CatCenter C) (X Y : C)

/-- The scalar multiplication by `R` on the type `X ⟶ Y` of morphisms in
a category `C` equipped with a ring morphism `R →+* CatCenter C`. -/
@[instance_reducible]
/-
**CategoryTheory.Linear.smulOfRingMorphism** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Linear`。
形式化陈述：smulOfRingMorphism : SMul R (X ⟶ Y) where smul a f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The scalar multiplication by `R` on the type `X ⟶ Y` of morphisms in
a category `C` equipped with a ring morphism `R →+* CatCenter C`.
-/
def smulOfRingMorphism : SMul R (X ⟶ Y) where
  smul a f := (φ a).app X ≫ f

variable {X Y}
/-
**CategoryTheory.Linear.smulOfRingMorphism_smul_eq** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Linear`。
形式化陈述：smulOfRingMorphism_smul_eq (a : R) (f : X ⟶ Y) : letI
参数：a : R；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smulOfRingMorphism_smul_eq (a : R) (f : X ⟶ Y) :
    letI := smulOfRingMorphism φ X Y
    a • f = (φ a).app X ≫ f := rfl

/-- `a • f = f ≫ (φ a).app Y`. -/
/-
**CategoryTheory.Linear.smulOfRingMorphism_smul_eq'** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Linear`。
形式化陈述：smulOfRingMorphism_smul_eq' (a : R) (f : X ⟶ Y) : letI
参数：a : R；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Linear.smulOfRingMorphism_smul_eq`：smulOfRingMorphism_smu
l_eq (a : R) (f : X ⟶ Y) : letI
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.CatCenter.naturality`：naturality (z : CatCenter C) {X Y :
 C} (f : X ⟶ Y) : f ≫ z.app Y = z.app X ≫ f

--- 原说明 ---
`a • f = f ≫ (φ a).app Y`.
-/
lemma smulOfRingMorphism_smul_eq' (a : R) (f : X ⟶ Y) :
    letI := smulOfRingMorphism φ X Y
    a • f = f ≫ (φ a).app Y := by
  rw [smulOfRingMorphism_smul_eq]
  exact ((φ a).naturality f).symm

variable (X Y)

set_option backward.isDefEq.respectTransparency false in
/-- The `R`-module structure on the type `X ⟶ Y` of morphisms in
a category `C` equipped with a ring morphism `R →+* CatCenter C`. -/
@[instance_reducible]
/-
**CategoryTheory.Linear.homModuleOfRingMorphism** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Linear`。
形式化陈述：homModuleOfRingMorphism : Module R (X ⟶ Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-module structure on the type `X ⟶ Y` of morphisms in
a category `C` equipped with a ring morphism `R →+* CatCenter C`.
-/
def homModuleOfRingMorphism : Module R (X ⟶ Y) := by
  letI := smulOfRingMorphism φ X Y
  exact
  { one_smul := fun a => by
      simp only [smulOfRingMorphism_smul_eq,
        Functor.id_obj, map_one, End.one_def, NatTrans.id_app, id_comp]
    mul_smul := fun a b f => by
      simp only [smulOfRingMorphism_smul_eq', Functor.id_obj, map_mul, End.mul_def,
        NatTrans.comp_app, assoc]
    smul_zero := fun a => by
      simp only [smulOfRingMorphism_smul_eq, comp_zero]
    zero_smul := fun a => by
      simp only [smulOfRingMorphism_smul_eq, map_zero,
        zero_app, zero_comp]
    smul_add := fun a b => by
      simp [smulOfRingMorphism_smul_eq]
    add_smul := fun a b f => by
      simp [smulOfRingMorphism_smul_eq] }

/-- The `R`-linear structure on a preadditive category `C` equipped with
a ring morphism `R →+* CatCenter C`. -/
@[instance_reducible]
/-
**CategoryTheory.Linear.ofRingMorphism** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Linear`。
形式化陈述：ofRingMorphism : Linear R C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-linear structure on a preadditive category `C` equipped with
a ring morphism `R →+* CatCenter C`.
-/
def ofRingMorphism : Linear R C := by
  letI := homModuleOfRingMorphism φ
  exact
    { smul_comp := fun X Y Z r f g => by simp only [smulOfRingMorphism_smul_eq, assoc]
      comp_smul := fun X Y Z f r g => by simp only [smulOfRingMorphism_smul_eq', assoc] }

end

end Linear

end CategoryTheory

