/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Additive

/-!
# The restriction functor of an embedding of complex shapes

Given `c` and `c'` complex shapes on two types, and `e : c.Embedding c'`
(satisfying `[e.IsRelIff]`), we define the restriction functor
`e.restrictionFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c`.

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsRelIff]

/-- Given `K : HomologicalComplex C c'` and `e : c.Embedding c'` (satisfying `[e.IsRelIff]`),
this is the homological complex in `HomologicalComplex C c` obtained by restriction. -/
@[simps]
/-
**HomologicalComplex.restriction** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：restriction : HomologicalComplex C c where X i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `K : HomologicalComplex C c'` and `e : c.Embedding c'` (satisfying `[e.IsR
elIff]`),
this is the homological complex in `HomologicalComplex C c` obtained by restrict
ion.
-/
def restriction : HomologicalComplex C c where
  X i := K.X (e.f i)
  d _ _ := K.d _ _
  shape i j hij := K.shape _ _ (by simpa only [← e.rel_iff] using hij)

/-- The isomorphism `(K.restriction e).X i ≅ K.X i'` when `e.f i = i'`. -/
/-
**HomologicalComplex.restrictionXIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：restrictionXIso {i : ι} {i' : ι'} (h : e.f i = i') : (K.restriction e).X i
 ≅ K.X i'
参数：h : e.f i = i'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(K.restriction e).X i ≅ K.X i'` when `e.f i = i'`.
-/
def restrictionXIso {i : ι} {i' : ι'} (h : e.f i = i') :
    (K.restriction e).X i ≅ K.X i' :=
  eqToIso (h ▸ rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**HomologicalComplex.restriction_d_eq** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：restriction_d_eq {i j : ι} {i' j' : ι'} (hi : e.f i = i') (hj : e.f j = j'
) : (K.restriction e).d i j = (K.restrictionXIso e hi).hom ≫ K.d i' j' ≫ (K.rest
rictionXIso e hj).inv
参数：hi : e.f i = i'；hj : e.f j = j'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restriction_d_eq {i j : ι} {i' j' : ι'} (hi : e.f i = i') (hj : e.f j = j') :
    (K.restriction e).d i j = (K.restrictionXIso e hi).hom ≫ K.d i' j' ≫
      (K.restrictionXIso e hj).inv := by
  subst hi hj
  simp [restrictionXIso]

variable {K L}

set_option backward.defeqAttrib.useBackward true in
/-- The morphism `K.restriction e ⟶ L.restriction e` induced by a morphism `φ : K ⟶ L`. -/
@[simps]
/-
**HomologicalComplex.restrictionMap** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x`。
形式化陈述：restrictionMap : K.restriction e ⟶ L.restriction e where f i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `K.restriction e ⟶ L.restriction e` induced by a morphism `φ : K ⟶ 
L`.
-/
def restrictionMap : K.restriction e ⟶ L.restriction e where
  f i := φ.f (e.f i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**HomologicalComplex.restrictionMap_f'** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：restrictionMap_f' {i : ι} {i' : ι'} (hi : e.f i = i') : (restrictionMap φ 
e).f i = (K.restrictionXIso e hi).hom ≫ φ.f i' ≫ (L.restrictionXIso e hi).inv
参数：hi : e.f i = i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrictionMap_f' {i : ι} {i' : ι'} (hi : e.f i = i') :
    (restrictionMap φ e).f i = (K.restrictionXIso e hi).hom ≫
      φ.f i' ≫ (L.restrictionXIso e hi).inv := by
  subst hi
  simp [restrictionXIso]

variable (K)

@[simp]
/-
**HomologicalComplex.restrictionMap_id** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：restrictionMap_id : restrictionMap (𝟙 K) e = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictionMap_id : restrictionMap (𝟙 K) e = 𝟙 _ := rfl

@[simp, reassoc]
/-
**HomologicalComplex.restrictionMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex`。
形式化陈述：restrictionMap_comp : restrictionMap (φ ≫ φ') e = restrictionMap φ e ≫ res
trictionMap φ' e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictionMap_comp :
    restrictionMap (φ ≫ φ') e = restrictionMap φ e ≫ restrictionMap φ' e := rfl

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') (C : Type*) [Category* C] [HasZeroObject C] [e.IsRelIff]

/-- Given `e : ComplexShape.Embedding c c'`, this is the restriction
functor `HomologicalComplex C c' ⥤ HomologicalComplex C c`. -/
@[simps]
/-
**ComplexShape.Embedding.restrictionFunctor** 是 Mathlib 中的一个定义，位于命名空间 `ComplexSh
ape.Embedding`。
形式化陈述：restrictionFunctor [HasZeroMorphisms C] : HomologicalComplex C c' ⥤ Homolo
gicalComplex C c where obj K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `e : ComplexShape.Embedding c c'`, this is the restriction
functor `HomologicalComplex C c' ⥤ HomologicalComplex C c`.
-/
def restrictionFunctor [HasZeroMorphisms C] :
    HomologicalComplex C c' ⥤ HomologicalComplex C c where
  obj K := K.restriction e
  map φ := HomologicalComplex.restrictionMap φ e
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroMorphisms C] : (e.restrictionFunctor C).PreservesZeroMorphisms where
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] : (e.restrictionFunctor C).Additive where

end ComplexShape.Embedding

