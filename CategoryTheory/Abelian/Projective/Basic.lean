/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Projective objects in abelian categories

In an abelian category, an object `P` is projective iff the functor
`preadditiveCoyonedaObj P` preserves finite colimits.

-/

public section

universe v u

namespace CategoryTheory

open Limits Projective Opposite

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The preadditive co-Yoneda functor on `P` preserves homology if `P` is projective. -/
/-
**CategoryTheory.preservesHomology_preadditiveCoyonedaObj_of_projective** 是 Math
lib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：preservesHomology_preadditiveCoyonedaObj_of_projective (P : C) [hP : Proje
ctive P] : (preadditiveCoyonedaObj P).PreservesHomology
参数：P : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditi
veCoyonedaObj`：projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj (P : 
C) : Projective P ↔ (preadditiveCoyonedaObj P).PreservesEpimorphisms
· 使用引理 `CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels`：p
reservesHomology_of_preservesEpis_and_kernels [PreservesZeroMorphisms L] [Preser
vesEpimorphisms L] [forall {X Y} (f : X ⟶ Y), PreservesLimi…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.additive_coyonedaObj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (X : C),   (Catego
ryTheory.preadditiveCoyon…
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
The preadditive co-Yoneda functor on `P` preserves homology if `P` is projective
.
-/
noncomputable instance preservesHomology_preadditiveCoyonedaObj_of_projective
    (P : C) [hP : Projective P] :
    (preadditiveCoyonedaObj P).PreservesHomology := by
  have := (projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj P).mp hP
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

/-- The preadditive co-Yoneda functor on `P` preserves finite colimits if `P` is projective. -/
/-
**CategoryTheory.preservesFiniteColimits_preadditiveCoyonedaObj_of_projective** 
是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：preservesFiniteColimits_preadditiveCoyonedaObj_of_projective (P : C) [hP :
 Projective P] : PreservesFiniteColimits (preadditiveCoyonedaObj P)
参数：P : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology`：pre
servesFiniteColimits_of_preservesHomology [HasFiniteCoproducts C] [HasCokernels 
C] : PreservesFiniteColimits F
· 使用定理 `CategoryTheory.additive_coyonedaObj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (X : C),   (Catego
ryTheory.preadditiveCoyon…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C

--- 原说明 ---
The preadditive co-Yoneda functor on `P` preserves finite colimits if `P` is pro
jective.
-/
noncomputable instance preservesFiniteColimits_preadditiveCoyonedaObj_of_projective
    (P : C) [hP : Projective P] :
    PreservesFiniteColimits (preadditiveCoyonedaObj P) := by
  apply Functor.preservesFiniteColimits_of_preservesHomology

/-- An object is projective if its preadditive co-Yoneda functor preserves finite colimits. -/
/-
**CategoryTheory.projective_of_preservesFiniteColimits_preadditiveCoyonedaObj** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：projective_of_preservesFiniteColimits_preadditiveCoyonedaObj (P : C) [hP :
 PreservesFiniteColimits (preadditiveCoyonedaObj P)] : Projective P
参数：P : C；preadditiveCoyonedaObj P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditi
veCoyonedaObj`：projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj (P : 
C) : Projective P ↔ (preadditiveCoyonedaObj P).PreservesEpimorphisms
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.additive_coyonedaObj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (X : C),   (Catego
ryTheory.preadditiveCoyon…
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
An object is projective if its preadditive co-Yoneda functor preserves finite co
limits.
-/
theorem projective_of_preservesFiniteColimits_preadditiveCoyonedaObj (P : C)
    [hP : PreservesFiniteColimits (preadditiveCoyonedaObj P)] : Projective P := by
  rw [projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj]
  have := Functor.preservesHomologyOfExact (preadditiveCoyonedaObj P)
  infer_instance

end CategoryTheory

