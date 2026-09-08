/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.DifferentialObject

/-!
# Homological complexes are differential graded objects.

We verify that a `HomologicalComplex` indexed by an `AddCommGroup` is
essentially the same thing as a differential graded object.

This equivalence is probably not particularly useful in practice;
it's here to check that definitions match up as expected.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-!
We first prove some results about differential graded objects.

TODO: We should move these to their own file.
-/
namespace CategoryTheory.DifferentialObject

variable {β : Type*} [AddCommGroup β] {b : β}
variable {V : Type*} [Category* V] [HasZeroMorphisms V]
variable (X : DifferentialObject ℤ (GradedObjectWithShift b V))

/-- Since `eqToHom` only preserves the fact that `X.X i = X.X j` but not `i = j`, this definition
is used to aid the simplifier. -/
/-
**CategoryTheory.DifferentialObject.objEqToHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.DifferentialObject`。
形式化陈述：objEqToHom {i j : β} (h : i = j) : X.obj i ⟶ X.obj j
参数：h : i = j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since `eqToHom` only preserves the fact that `X.X i = X.X j` but not `i = j`, th
is definition
is used to aid the simplifier.
-/
abbrev objEqToHom {i j : β} (h : i = j) :
    X.obj i ⟶ X.obj j :=
  eqToHom (congr_arg X.obj h)

@[simp]
/-
**CategoryTheory.DifferentialObject.objEqToHom_refl** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.DifferentialObject`。
形式化陈述：objEqToHom_refl (i : β) : X.objEqToHom (refl i) = 𝟙 _
参数：i : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
-/
theorem objEqToHom_refl (i : β) : X.objEqToHom (refl i) = 𝟙 _ :=
  rfl

-- Removing `@[simp]`, because it is in the opposite direction of `eqToHom_naturality`.
-- Having both causes an infinite loop in the simpNF linter.
set_option backward.isDefEq.respectTransparency false in -- Needed in dgoToHomologicalComplex
@[reassoc]
/-
**CategoryTheory.DifferentialObject.objEqToHom_d** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.DifferentialObject`。
形式化陈述：objEqToHom_d {x y : β} (h : x = y) : X.objEqToHom h ≫ X.d y = X.d x ≫ X.ob
jEqToHom (by cases h; rfl)
参数：h : x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem objEqToHom_d {x y : β} (h : x = y) :
    X.objEqToHom h ≫ X.d y = X.d x ≫ X.objEqToHom (by cases h; rfl) := by cases h; simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.DifferentialObject.d_squared_apply** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.DifferentialObject`。
形式化陈述：d_squared_apply {x : β} : X.d x ≫ X.d _ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.DifferentialObject.d_squared`：∀ {S : Type u_1} [inst : Ad
dMonoidWithOne S] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   [in
st_2 : CategoryTheory.Limits.HasZ…
-/
theorem d_squared_apply {x : β} : X.d x ≫ X.d _ = 0 := congr_fun X.d_squared _

-- Removing `@[simp]`, because it is in the opposite direction of `eqToHom_naturality`.
-- Having both causes an infinite loop in the simpNF linter.
@[reassoc]
/-
**CategoryTheory.DifferentialObject.eqToHom_f'** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.DifferentialObject`。
形式化陈述：eqToHom_f' {X Y : DifferentialObject Int (GradedObjectWithShift b V)} (f :
 X ⟶ Y) {x y : β} (h : x = y) : X.objEqToHom h ≫ f.f y = f.f x ≫ Y.objEqToHom h
参数：GradedObjectWithShift b V；f : X ⟶ Y；h : x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem eqToHom_f' {X Y : DifferentialObject ℤ (GradedObjectWithShift b V)} (f : X ⟶ Y) {x y : β}
    (h : x = y) : X.objEqToHom h ≫ f.f y = f.f x ≫ Y.objEqToHom h := by cases h; simp

end CategoryTheory.DifferentialObject

open CategoryTheory.DifferentialObject

namespace HomologicalComplex

variable {β : Type*} [AddCommGroup β] (b : β)
variable (V : Type*) [Category* V] [HasZeroMorphisms V]

@[reassoc]
/-
**HomologicalComplex.d_eqToHom** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：d_eqToHom (X : HomologicalComplex V (ComplexShape.up' b)) {x y z : β} (h :
 y = z) : X.d x y ≫ eqToHom (congr_arg X.X h) = X.d x z
参数：X : HomologicalComplex V (ComplexShape.up' b)；h : y = z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem d_eqToHom (X : HomologicalComplex V (ComplexShape.up' b)) {x y z : β} (h : y = z) :
    X.d x y ≫ eqToHom (congr_arg X.X h) = X.d x z := by cases h; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- The functor from differential graded objects to homological complexes.
-/
@[simps]
/-
**HomologicalComplex.dgoToHomologicalComplex** 是 Mathlib 中的一个定义，位于命名空间 `Homologi
calComplex`。
形式化陈述：dgoToHomologicalComplex : DifferentialObject Int (GradedObjectWithShift b 
V) ⥤ HomologicalComplex V (ComplexShape.up' b) where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from differential graded objects to homological complexes.
-/
def dgoToHomologicalComplex :
    DifferentialObject ℤ (GradedObjectWithShift b V) ⥤
      HomologicalComplex V (ComplexShape.up' b) where
  obj X :=
    { X := fun i => X.obj i
      d := fun i j =>
        if h : i + b = j then X.d i ≫ X.objEqToHom (show i + (1 : ℤ) • b = j by simp [h]) else 0
      shape := fun i j w => by dsimp at w; convert! dif_neg w
      d_comp_d' := fun i j k hij hjk => by
        dsimp at hij hjk; subst hij hjk
        simp [objEqToHom_d_assoc] }
  map {X Y} f :=
    { f := f.f
      comm' := fun i j h => by
        dsimp at h ⊢
        subst h
        have : f.f i ≫ Y.d i = X.d i ≫ f.f _ := (congr_fun f.comm i).symm
        simp only [dite_true, Category.assoc, eqToHom_f', reassoc_of% this] }

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor from homological complexes to differential graded objects.
-/
@[simps]
/-
**HomologicalComplex.homologicalComplexToDGO** 是 Mathlib 中的一个定义，位于命名空间 `Homologi
calComplex`。
形式化陈述：homologicalComplexToDGO : HomologicalComplex V (ComplexShape.up' b) ⥤ Diff
erentialObject Int (GradedObjectWithShift b V) where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from homological complexes to differential graded objects.
-/
def homologicalComplexToDGO :
    HomologicalComplex V (ComplexShape.up' b) ⥤
      DifferentialObject ℤ (GradedObjectWithShift b V) where
  obj X :=
    { obj := fun i => X.X i
      d := fun i => X.d i _ }
  map {X Y} f := { f := f.f }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit isomorphism for `dgoEquivHomologicalComplex`.
-/
@[simps!]
/-
**HomologicalComplex.dgoEquivHomologicalComplexUnitIso** 是 Mathlib 中的一个定义，位于命名空间
 `HomologicalComplex`。
形式化陈述：dgoEquivHomologicalComplexUnitIso : 𝟭 (DifferentialObject Int (GradedObjec
tWithShift b V)) ≅ dgoToHomologicalComplex b V ⋙ homologicalComplexToDGO b V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit isomorphism for `dgoEquivHomologicalComplex`.
-/
def dgoEquivHomologicalComplexUnitIso :
    𝟭 (DifferentialObject ℤ (GradedObjectWithShift b V)) ≅
      dgoToHomologicalComplex b V ⋙ homologicalComplexToDGO b V :=
  NatIso.ofComponents (fun X =>
    { hom := { f := fun i => 𝟙 (X.obj i) }
      inv := { f := fun i => 𝟙 (X.obj i) } })

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The counit isomorphism for `dgoEquivHomologicalComplex`.
-/
@[simps!]
/-
**HomologicalComplex.dgoEquivHomologicalComplexCounitIso** 是 Mathlib 中的一个定义，位于命名
空间 `HomologicalComplex`。
形式化陈述：dgoEquivHomologicalComplexCounitIso : homologicalComplexToDGO b V ⋙ dgoToH
omologicalComplex b V ≅ 𝟭 (HomologicalComplex V (ComplexShape.up' b))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit isomorphism for `dgoEquivHomologicalComplex`.
-/
def dgoEquivHomologicalComplexCounitIso :
    homologicalComplexToDGO b V ⋙ dgoToHomologicalComplex b V ≅
      𝟭 (HomologicalComplex V (ComplexShape.up' b)) :=
  NatIso.ofComponents (fun X =>
    { hom := { f := fun i => 𝟙 (X.X i) }
      inv := { f := fun i => 𝟙 (X.X i) } })

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The category of differential graded objects in `V` is equivalent
to the category of homological complexes in `V`.
-/
@[simps]
/-
**HomologicalComplex.dgoEquivHomologicalComplex** 是 Mathlib 中的一个定义，位于命名空间 `Homol
ogicalComplex`。
形式化陈述：dgoEquivHomologicalComplex : DifferentialObject Int (GradedObjectWithShift
 b V) ≌ HomologicalComplex V (ComplexShape.up' b) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of differential graded objects in `V` is equivalent
to the category of homological complexes in `V`.
-/
def dgoEquivHomologicalComplex :
    DifferentialObject ℤ (GradedObjectWithShift b V) ≌
      HomologicalComplex V (ComplexShape.up' b) where
  functor := dgoToHomologicalComplex b V
  inverse := homologicalComplexToDGO b V
  unitIso := dgoEquivHomologicalComplexUnitIso b V
  counitIso := dgoEquivHomologicalComplexCounitIso b V

end HomologicalComplex

