/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GradedObject

/-!
# The graded object in a single degree

In this file, we define the functor `GradedObject.single j : C ⥤ GradedObject J C`
which sends an object `X : C` to the graded object which is `X` in degree `j` and
the initial object of `C` in other degrees.

-/

@[expose] public section

namespace CategoryTheory

open Limits

namespace GradedObject

variable {J : Type*} {C : Type*} [Category* C] [HasInitial C] [DecidableEq J]

/-- The functor which sends `X : C` to the graded object which is `X` in degree `j`
and the initial object in other degrees. -/
/-
**CategoryTheory.GradedObject.single** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.G
radedObject`。
形式化陈述：single (j : J) : C ⥤ GradedObject J C where obj X i
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which sends `X : C` to the graded object which is `X` in degree `j`
and the initial object in other degrees.
-/
noncomputable def single (j : J) : C ⥤ GradedObject J C where
  obj X i := if i = j then X else ⊥_ C
  map {X₁ X₂} f i :=
    if h : i = j then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else eqToHom (by dsimp; rw [if_neg h, if_neg h])

variable (J) in
/-- The functor which sends `X : C` to the graded object which is `X` in degree `0`
and the initial object in nonzero degrees. -/
/-
**CategoryTheory.GradedObject.single** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.G
radedObject`。
形式化陈述：single (j : J) : C ⥤ GradedObject J C where obj X i
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which sends `X : C` to the graded object which is `X` in degree `0`
and the initial object in nonzero degrees.
-/
noncomputable abbrev single₀ [Zero J] : C ⥤ GradedObject J C := single 0

/-- The canonical isomorphism `(single j).obj X i ≅ X` when `i = j`. -/
/-
**CategoryTheory.GradedObject.singleObjApplyIsoOfEq** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.GradedObject`。
形式化陈述：singleObjApplyIsoOfEq (j : J) (X : C) (i : J) (h : i = j) : (single j).obj
 X i ≅ X
参数：j : J；X : C；i : J；h : i = j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(single j).obj X i ≅ X` when `i = j`.
-/
noncomputable def singleObjApplyIsoOfEq (j : J) (X : C) (i : J) (h : i = j) :
    (single j).obj X i ≅ X := eqToIso (if_pos h)

/-- The canonical isomorphism `(single j).obj X j ≅ X`. -/
/-
**CategoryTheory.GradedObject.singleObjApplyIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.GradedObject`。
形式化陈述：singleObjApplyIso (j : J) (X : C) : (single j).obj X j ≅ X
参数：j : J；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(single j).obj X j ≅ X`.
-/
noncomputable abbrev singleObjApplyIso (j : J) (X : C) :
    (single j).obj X j ≅ X := singleObjApplyIsoOfEq j X j rfl

/-- The object `(single j).obj X i` is initial when `i ≠ j`. -/
/-
**CategoryTheory.GradedObject.isInitialSingleObjApply** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.GradedObject`。
形式化陈述：isInitialSingleObjApply (j : J) (X : C) (i : J) (h : i != j) : IsInitial (
(single j).obj X i)
参数：j : J；X : C；i : J；h : i != j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object `(single j).obj X i` is initial when `i ≠ j`.
-/
noncomputable def isInitialSingleObjApply (j : J) (X : C) (i : J) (h : i ≠ j) :
    IsInitial ((single j).obj X i) := by
  dsimp [single]
  rw [if_neg h]
  exact initialIsInitial
/-
**CategoryTheory.GradedObject.singleObjApplyIsoOfEq_inv_single_map** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：singleObjApplyIsoOfEq_inv_single_map (j : J) {X Y : C} (f : X ⟶ Y) (i : J)
 (h : i = j) : (singleObjApplyIsoOfEq j X i h).inv ≫ (single j).map f i = f ≫ (s
ingleObjApplyIsoOfEq j Y i h).inv
参数：j : J；f : X ⟶ Y；i : J；h : i = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma singleObjApplyIsoOfEq_inv_single_map (j : J) {X Y : C} (f : X ⟶ Y) (i : J) (h : i = j) :
    (singleObjApplyIsoOfEq j X i h).inv ≫ (single j).map f i =
      f ≫ (singleObjApplyIsoOfEq j Y i h).inv := by
  subst h
  simp [singleObjApplyIsoOfEq, single]
/-
**CategoryTheory.GradedObject.single_map_singleObjApplyIsoOfEq_hom** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：single_map_singleObjApplyIsoOfEq_hom (j : J) {X Y : C} (f : X ⟶ Y) (i : J)
 (h : i = j) : (single j).map f i ≫ (singleObjApplyIsoOfEq j Y i h).hom = (singl
eObjApplyIsoOfEq j X i h).hom ≫ f
参数：j : J；f : X ⟶ Y；i : J；h : i = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma single_map_singleObjApplyIsoOfEq_hom (j : J) {X Y : C} (f : X ⟶ Y) (i : J) (h : i = j) :
    (single j).map f i ≫ (singleObjApplyIsoOfEq j Y i h).hom =
      (singleObjApplyIsoOfEq j X i h).hom ≫ f := by
  subst h
  simp [singleObjApplyIsoOfEq, single]

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.singleObjApplyIso_inv_single_map** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：singleObjApplyIso_inv_single_map (j : J) {X Y : C} (f : X ⟶ Y) : (singleOb
jApplyIso j X).inv ≫ (single j).map f j = f ≫ (singleObjApplyIso j Y).inv
参数：j : J；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.singleObjApplyIsoOfEq_inv_single_map`：single
ObjApplyIsoOfEq_inv_single_map (j : J) {X Y : C} (f : X ⟶ Y) (i : J) (h : i = j)
 : (singleObjApplyIsoOfEq j X i h).inv ≫ (single j).ma…
-/
lemma singleObjApplyIso_inv_single_map (j : J) {X Y : C} (f : X ⟶ Y) :
    (singleObjApplyIso j X).inv ≫ (single j).map f j = f ≫ (singleObjApplyIso j Y).inv := by
  apply singleObjApplyIsoOfEq_inv_single_map

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.single_map_singleObjApplyIso_hom** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：single_map_singleObjApplyIso_hom (j : J) {X Y : C} (f : X ⟶ Y) : (single j
).map f j ≫ (singleObjApplyIso j Y).hom = (singleObjApplyIso j X).hom ≫ f
参数：j : J；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.single_map_singleObjApplyIsoOfEq_hom`：single
_map_singleObjApplyIsoOfEq_hom (j : J) {X Y : C} (f : X ⟶ Y) (i : J) (h : i = j)
 : (single j).map f i ≫ (singleObjApplyIsoOfEq j Y i h…
-/
lemma single_map_singleObjApplyIso_hom (j : J) {X Y : C} (f : X ⟶ Y) :
    (single j).map f j ≫ (singleObjApplyIso j Y).hom = (singleObjApplyIso j X).hom ≫ f := by
  apply single_map_singleObjApplyIsoOfEq_hom

set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The composition of the single functor `single j : C ⥤ GradedObject J C` and the
evaluation functor `eval j` identifies to the identity functor. -/
@[simps!]
/-
**CategoryTheory.GradedObject.singleCompEval** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.GradedObject`。
形式化陈述：singleCompEval (j : J) : single j ⋙ eval j ≅ 𝟭 C
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of the single functor `single j : C ⥤ GradedObject J C` and the
evaluation functor `eval j` identifies to the identity functor.
-/
noncomputable def singleCompEval (j : J) : single j ⋙ eval j ≅ 𝟭 C :=
  NatIso.ofComponents (singleObjApplyIso j) (by simp)

end GradedObject

end CategoryTheory

