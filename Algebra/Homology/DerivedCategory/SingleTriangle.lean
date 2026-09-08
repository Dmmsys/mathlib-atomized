/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The distinguished triangle of a short exact sequence in an abelian category

Given a short exact short complex `S` in an abelian category, we construct
the associated distinguished triangle in the derived category:
`(singleFunctor C 0).obj S.X₁ ⟶ (singleFunctor C 0).obj S.X₂ ⟶ (singleFunctor C 0).obj S.X₃ ⟶ ...`

## TODO
* when the canonical t-structure on the derived category is formalized, refactor
  this definition to make it a particular case of the triangle induced by a short
  exact sequence in the heart of a t-structure

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open Category DerivedCategory Pretriangulated

namespace ShortComplex

variable {S : ShortComplex C} (hS : S.ShortExact)

namespace ShortExact

/-- The connecting homomorphism
`(singleFunctor C 0).obj S.X₃ ⟶ ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧` in the derived
category of `C` when `S` is a short exact short complex in `C`. -/
/-
**CategoryTheory.ShortComplex.ShortExact.single** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connecting homomorphism
`(singleFunctor C 0).obj S.X₃ ⟶ ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧` in the 
derived
category of `C` when `S` is a short exact short complex in `C`.
-/
noncomputable def singleδ : (singleFunctor C 0).obj S.X₃ ⟶
    ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧ :=
  (((SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)).hom.app S.X₃) ≫
    triangleOfSESδ (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) ≫
    (((SingleFunctors.evaluation _ _ 0).mapIso
      (singleFunctorsPostcompQIso C)).inv.app S.X₁)⟦(1 : ℤ)⟧'

/-- The (distinguished) triangle in the derived category of `C` given by a
short exact short complex in `C`. -/
@[simps!]
/-
**CategoryTheory.ShortComplex.ShortExact.singleTriangle** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：singleTriangle : Triangle (DerivedCategory C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (distinguished) triangle in the derived category of `C` given by a
short exact short complex in `C`.
-/
noncomputable def singleTriangle : Triangle (DerivedCategory C) :=
  Triangle.mk ((singleFunctor C 0).map S.f)
    ((singleFunctor C 0).map S.g) hS.singleδ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a short exact complex `S` in `C` that is short exact (`hS`), this is the
canonical isomorphism between the triangle `hS.singleTriangle` in the derived category
and the triangle attached to the corresponding short exact sequence of cochain complexes
after the application of the single functor. -/
@[simps!]
/-
**CategoryTheory.ShortComplex.ShortExact.singleTriangleIso** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：singleTriangleIso : hS.singleTriangle ≅ triangleOfSES (hS.map_of_exact (Ho
mologicalComplex.single C (ComplexShape.up Int) 0))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
Given a short exact complex `S` in `C` that is short exact (`hS`), this is the
canonical isomorphism between the triangle `hS.singleTriangle` in the derived ca
tegory
and the triangle attached to the corresponding short exact sequence of cochain c
omplexes
after the application of the single functor.
-/
noncomputable def singleTriangleIso :
    hS.singleTriangle ≅
      triangleOfSES (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) := by
  let e := (SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)
  refine Triangle.isoMk _ _ (e.app S.X₁) (e.app S.X₂) (e.app S.X₃) ?_ ?_ ?_
  · cat_disch
  · cat_disch
  · simp [singleδ, e, ← Functor.map_comp, CochainComplex.singleFunctors]

/-- The distinguished triangle in the derived category of `C` given by a
short exact short complex in `C`. -/
/-
**CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：singleTriangle_distinguished : hS.singleTriangle in distTriang (DerivedCat
egory C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsSingle`：∀ {V : Type u} [ins
t : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms V]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.map_of_exact`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `HomologicalComplex.instPreservesFiniteLimitsSingle`：∀ {C : Type u_1} {ι 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c : ComplexShape ι}  
 [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `HomologicalComplex.instPreservesFiniteColimitsSingle`：∀ {C : Type u_1} {
ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c : ComplexShape ι}
   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用引理 `DerivedCategory.triangleOfSES_distinguished`：triangleOfSES_distinguished
 : triangleOfSES hS in distTriang (DerivedCategory C)

--- 原说明 ---
The distinguished triangle in the derived category of `C` given by a
short exact short complex in `C`.
-/
lemma singleTriangle_distinguished :
    hS.singleTriangle ∈ distTriang (DerivedCategory C) :=
  isomorphic_distinguished _ (triangleOfSES_distinguished (hS.map_of_exact
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0))) _ (singleTriangleIso hS)

variable {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism `h₁.singleTriangle h₁ ⟶ h₂.singleTriangle` that is induced by a
map of short exact sequences of objects of `C`.
-/
@[simps!]
/-
**CategoryTheory.ShortComplex.ShortExact.singleTriangle.map** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.ShortComplex.ShortExact.singleTriangle`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       [inst_2 : HasDerivedCategory C] →         {S₁
 S₂ : CategoryTheory.ShortComplex C} →           (h₁ : S₁.ShortExact) → (h₂ : S₂
.ShortExact) → (S₁ ⟶ S₂) → (h₁.singleTriangle ⟶ h₂.singleTriangle)
参数：h₁ : S₁.ShortExact；h₂ : S₂.ShortExact；S₁ ⟶ S₂；h₁.singleTriangle ⟶ h₂.singleTr
iangle。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `h₁.singleTriangle h₁ ⟶ h₂.singleTriangle` that is induced by a
map of short exact sequences of objects of `C`.
-/
noncomputable def singleTriangle.map : h₁.singleTriangle ⟶ h₂.singleTriangle where
  hom₁ := (singleFunctor C 0).map f.τ₁
  hom₂ := (singleFunctor C 0).map f.τ₂
  hom₃ := (singleFunctor C 0).map f.τ₃
  comm₁ := by simp [← Functor.map_comp, f.comm₁₂]
  comm₂ := by simp [← Functor.map_comp, f.comm₂₃]
  comm₃ := by
    dsimp [singleδ]
    rw [assoc, assoc, ← Functor.map_comp, ← NatTrans.naturality, Functor.map_comp]
    dsimp [CochainComplex.singleFunctors]
    rw [reassoc_of% dsimp% ((triangleOfSES.map (h₁.map_of_exact _) (h₂.map_of_exact _))
      ((HomologicalComplex.single C (.up ℤ) 0).mapShortComplex.map f)).comm₃]
    simp

end ShortExact

end ShortComplex

end CategoryTheory

