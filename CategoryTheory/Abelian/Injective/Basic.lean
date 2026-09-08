/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Injective objects in abelian categories

* Objects in an abelian category are injective if and only if the preadditive Yoneda functor
  on them preserves finite colimits.
-/

public section


noncomputable section

open CategoryTheory Limits Injective Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The preadditive Yoneda functor on `J` preserves homology if `J` is injective. -/
/-
**CategoryTheory.preservesHomology_preadditiveYonedaObj_of_injective** 是 Mathlib
 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：preservesHomology_preadditiveYonedaObj_of_injective (J : C) [hJ : Injectiv
e J] : (preadditiveYonedaObj J).PreservesHomology
参数：J : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Injective.injective_iff_preservesEpimorphisms_preadditive
_yoneda_obj'`：injective_iff_preservesEpimorphisms_preadditive_yoneda_obj' (J : C
) : Injective J ↔ (preadditiveYonedaObj J).PreservesEpimorphisms
· 使用引理 `CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels`：p
reservesHomology_of_preservesEpis_and_kernels [PreservesZeroMorphisms L] [Preser
vesEpimorphisms L] [forall {X Y} (f : X ⟶ Y), PreservesLimi…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.additive_yonedaObj`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (X : C),   (Category
Theory.preadditiveYoned…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
The preadditive Yoneda functor on `J` preserves homology if `J` is injective.
-/
instance preservesHomology_preadditiveYonedaObj_of_injective (J : C) [hJ : Injective J] :
    (preadditiveYonedaObj J).PreservesHomology := by
  let := (injective_iff_preservesEpimorphisms_preadditive_yoneda_obj' J).mp hJ
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

/-- The preadditive Yoneda functor on `J` preserves colimits if `J` is injective. -/
/-
**CategoryTheory.preservesFiniteColimits_preadditiveYonedaObj_of_injective** 是 M
athlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：preservesFiniteColimits_preadditiveYonedaObj_of_injective (J : C) [hP : In
jective J] : PreservesFiniteColimits (preadditiveYonedaObj J)
参数：J : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology`：pre
servesFiniteColimits_of_preservesHomology [HasFiniteCoproducts C] [HasCokernels 
C] : PreservesFiniteColimits F
· 使用定理 `CategoryTheory.additive_yonedaObj`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (X : C),   (Category
Theory.preadditiveYoned…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C

--- 原说明 ---
The preadditive Yoneda functor on `J` preserves colimits if `J` is injective.
-/
instance preservesFiniteColimits_preadditiveYonedaObj_of_injective (J : C) [hP : Injective J] :
    PreservesFiniteColimits (preadditiveYonedaObj J) := by
  apply Functor.preservesFiniteColimits_of_preservesHomology

/-- An object is injective if its preadditive Yoneda functor preserves finite colimits. -/
/-
**CategoryTheory.injective_of_preservesFiniteColimits_preadditiveYonedaObj** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：injective_of_preservesFiniteColimits_preadditiveYonedaObj (J : C) [hP : Pr
eservesFiniteColimits (preadditiveYonedaObj J)] : Injective J
参数：J : C；preadditiveYonedaObj J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Injective.injective_iff_preservesEpimorphisms_preadditive
_yoneda_obj'`：injective_iff_preservesEpimorphisms_preadditive_yoneda_obj' (J : C
) : Injective J ↔ (preadditiveYonedaObj J).PreservesEpimorphisms
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.additive_yonedaObj`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (X : C),   (Category
Theory.preadditiveYoned…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesEpimorphisms`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `ModuleCat.instHasZeroObject`：∀ {R : Type u} [inst : Ring R], CategoryThe
ory.Limits.HasZeroObject (ModuleCat R)

--- 原说明 ---
An object is injective if its preadditive Yoneda functor preserves finite colimi
ts.
-/
theorem injective_of_preservesFiniteColimits_preadditiveYonedaObj (J : C)
    [hP : PreservesFiniteColimits (preadditiveYonedaObj J)] : Injective J := by
  rw [injective_iff_preservesEpimorphisms_preadditive_yoneda_obj']
  have := Functor.preservesHomologyOfExact (preadditiveYonedaObj J)
  infer_instance

end CategoryTheory

