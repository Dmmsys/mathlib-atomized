/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The category of homological complexes is linear

In this file, we define the instance `Linear R (HomologicalComplex C c)` when the
category `C` is `R`-linear.

## TODO

- show lemmas like `HomologicalComplex.homologyMap_smul` (after doing the same
  for short complexes in `Mathlib/Algebra/Homology/ShortComplex/Linear.lean`)

-/

public section

open CategoryTheory

variable {R : Type*} [Semiring R] {C D : Type*} [Category* C] [Preadditive C]
  [Category* D] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  {ι : Type*} {c : ComplexShape ι}

namespace HomologicalComplex

variable {X Y : HomologicalComplex C c}

/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R (X ⟶ Y) where
  smul r f := { f := fun n => r • f.f n }

@[simp]
/-
**HomologicalComplex.smul_f_apply** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`
。
形式化陈述：smul_f_apply (r : R) (f : X ⟶ Y) (n : ι) : (r • f).f n = r • f.f n
参数：r : R；f : X ⟶ Y；n : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_f_apply (r : R) (f : X ⟶ Y) (n : ι) : (r • f).f n = r • f.f n := rfl

@[simp]
/-
**HomologicalComplex.units_smul_f_apply** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：units_smul_f_apply (r : Rˣ) (f : X ⟶ Y) (n : ι) : (r • f).f n = r • f.f n
参数：r : Rˣ；f : X ⟶ Y；n : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma units_smul_f_apply (r : Rˣ) (f : X ⟶ Y) (n : ι) : (r • f).f n = r • f.f n := rfl
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : HomologicalComplex C c) : Module R (X ⟶ Y) where
  one_smul a := by cat_disch
  smul_zero := by cat_disch
  smul_add := by cat_disch
  zero_smul := by cat_disch
  add_smul _ _ _ := by ext; apply add_smul
  mul_smul _ _ _ := by ext; apply mul_smul
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Linear R (HomologicalComplex C c) where

end HomologicalComplex

/-
**CategoryTheory.Functor.mapHomologicalComplex_linear** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {C : Type u_2} {D : Type u_3} [inst_1
 : CategoryTheory.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Preadditive 
C] [inst_3 : CategoryTheory.Category.{v_2, u_3} D]   [inst_4 : CategoryTheory.Pr
eadditive D] [inst_5 : CategoryTheory.Linear R C] [inst_6 : CategoryTheory.Linea
r R D]   {ι : Type u_4} (F : CategoryTheory.Functor C D) [inst_7 : F.Additive] [
CategoryTheory.Functor.Linear R F]   (c : ComplexShape ι), CategoryTheory.Functo
r.Linear R (F.mapHomologicalComplex c)
参数：F : CategoryTheory.Functor C D；c : ComplexShape ι；F.mapHomologicalComplex c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.mapHomologicalComplex_map_f`：∀ {ι : Type u_1} {W₁
 : Type u_3} {W₂ : Type u_4} [inst : CategoryTheory.Category.{v_2, u_3} W₁]   [i
nst_1 : CategoryTheory.Category.{v_3, u_…
· 使用定理 `CategoryTheory.Functor.map_smul`：map_smul {X Y : C} (r : R) (f : X ⟶ Y) 
: F.map (r • f) = r • F.map f
-/
instance CategoryTheory.Functor.mapHomologicalComplex_linear
    (F : C ⥤ D) [F.Additive] [Functor.Linear R F] (c : ComplexShape ι) :
    Functor.Linear R (F.mapHomologicalComplex c) where
