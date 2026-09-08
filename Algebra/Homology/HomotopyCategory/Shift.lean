/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Shift.Quotient
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The shift on cochain complexes and on the homotopy category

In this file, we show that for any preadditive category `C`, the categories
`CochainComplex C ℤ` and `HomotopyCategory C (ComplexShape.up ℤ)` are
equipped with a shift by `ℤ`.

We also show that if `F : C ⥤ D` is an additive functor, then the functors
`F.mapHomologicalComplex (ComplexShape.up ℤ)` and
`F.mapHomotopyCategory (ComplexShape.up ℤ)` commute with the shift by `ℤ`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe v v' u u'

open CategoryTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

namespace CochainComplex

open HomologicalComplex

set_option backward.defeqAttrib.useBackward true in
/-- The shift functor by `n : ℤ` on `CochainComplex C ℤ` which sends a cochain
complex `K` to the complex which is `K.X (i + n)` in degree `i`, and which
multiplies the differentials by `(-1)^n`. -/
@[simps]
/-
**CochainComplex.shiftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：shiftFunctor (n : Int) : CochainComplex C Int ⥤ CochainComplex C Int where
 obj K
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shift functor by `n : ℤ` on `CochainComplex C ℤ` which sends a cochain
complex `K` to the complex which is `K.X (i + n)` in degree `i`, and which
multiplies the differentials by `(-1)^n`.
-/
def shiftFunctor (n : ℤ) : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K :=
    { X := fun i => K.X (i + n)
      d := fun _ _ => n.negOnePow • K.d _ _
      d_comp_d' := by
        intros
        simp only [Linear.comp_units_smul, Linear.units_smul_comp, d_comp_d, smul_zero]
      shape := fun i j hij => by
        rw [K.shape, smul_zero]
        intro hij'
        apply hij
        dsimp at hij' ⊢
        lia }
  map φ :=
    { f := fun _ => φ.f _
      comm' := by
        intros
        dsimp
        simp only [Linear.comp_units_smul, Hom.comm, Linear.units_smul_comp] }
  map_id := by intros; rfl
  map_comp := by intros; rfl
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (shiftFunctor C n).Additive where
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) {R : Type*} [Ring R] [Linear R C] :
    Functor.Linear R (shiftFunctor C n) where

variable {C}

/-- The canonical isomorphism `((shiftFunctor C n).obj K).X i ≅ K.X m` when `m = i + n`. -/
@[simp]
/-
**CochainComplex.shiftFunctorObjXIso** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：shiftFunctorObjXIso (K : CochainComplex C Int) (n i m : Int) (hm : m = i +
 n) : ((shiftFunctor C n).obj K).X i ≅ K.X m
参数：K : CochainComplex C Int；n i m : Int；hm : m = i + n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `((shiftFunctor C n).obj K).X i ≅ K.X m` when `m = i +
 n`.
-/
def shiftFunctorObjXIso (K : CochainComplex C ℤ) (n i m : ℤ) (hm : m = i + n) :
    ((shiftFunctor C n).obj K).X i ≅ K.X m := K.XIsoOfEq hm.symm

section

variable (C)

attribute [local simp] XIsoOfEq_hom_naturality

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The shift functor by `n` on `CochainComplex C ℤ` identifies to the identity
functor when `n = 0`. -/
@[simps!]
/-
**CochainComplex.shiftFunctorZero'** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：shiftFunctorZero' (n : Int) (h : n = 0) : shiftFunctor C n ≅ 𝟭 _
参数：n : Int；h : n = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shift functor by `n` on `CochainComplex C ℤ` identifies to the identity
functor when `n = 0`.
-/
def shiftFunctorZero' (n : ℤ) (h : n = 0) :
    shiftFunctor C n ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.shiftFunctorObjXIso _ _ _ (by lia))
    (fun _ _ _ => by simp [h])) (fun _ ↦ by ext; simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The compatibility of the shift functors on `CochainComplex C ℤ` with respect
to the addition of integers. -/
@[simps!]
/-
**CochainComplex.shiftFunctorAdd'** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：shiftFunctorAdd' (n₁ n₂ n₁₂ : Int) (h : n₁ + n₂ = n₁₂) : shiftFunctor C n₁
₂ ≅ shiftFunctor C n₁ ⋙ shiftFunctor C n₂
参数：n₁ n₂ n₁₂ : Int；h : n₁ + n₂ = n₁₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The compatibility of the shift functors on `CochainComplex C ℤ` with respect
to the addition of integers.
-/
def shiftFunctorAdd' (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂) :
    shiftFunctor C n₁₂ ≅ shiftFunctor C n₁ ⋙ shiftFunctor C n₂ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.shiftFunctorObjXIso _ _ _ (by lia))
    (fun _ _ _ => by
      subst h
      dsimp
      simp only [add_comm n₁ n₂, Int.negOnePow_add, Linear.units_smul_comp,
        Linear.comp_units_smul, d_comp_XIsoOfEq_hom, smul_smul, XIsoOfEq_hom_comp_d]))
    (by intros; ext; simp)

attribute [local simp] XIsoOfEq

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasShift (CochainComplex C ℤ) ℤ := hasShiftMk _ _
  { F := shiftFunctor C
    zero := shiftFunctorZero' C _ rfl
    add := fun n₁ n₂ => shiftFunctorAdd' C n₁ n₂ _ rfl }
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) :
    (CategoryTheory.shiftFunctor (HomologicalComplex C (ComplexShape.up ℤ)) n).Additive :=
  inferInstanceAs <| (CochainComplex.shiftFunctor C n).Additive
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) {R : Type*} [Ring R] [Linear R C] :
    Functor.Linear R
      (CategoryTheory.shiftFunctor (HomologicalComplex C (ComplexShape.up ℤ)) n) where

end

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CochainComplex.shiftFunctor_obj_X'** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：shiftFunctor_obj_X' (K : CochainComplex C Int) (n p : Int) : ((CategoryThe
ory.shiftFunctor (CochainComplex C Int) n).obj K).X p = K.X (p + n)
参数：K : CochainComplex C Int；n p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma shiftFunctor_obj_X' (K : CochainComplex C ℤ) (n p : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).obj K).X p = K.X (p + n) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CochainComplex.shiftFunctor_map_f'** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：shiftFunctor_map_f' {K L : CochainComplex C Int} (φ : K ⟶ L) (n p : Int) :
 ((CategoryTheory.shiftFunctor (CochainComplex C Int) n).map φ).f p = φ.f (p + n
)
参数：φ : K ⟶ L；n p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma shiftFunctor_map_f' {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n p : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).map φ).f p = φ.f (p + n) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CochainComplex.shiftFunctor_obj_d'** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：shiftFunctor_obj_d' (K : CochainComplex C Int) (n i j : Int) : ((CategoryT
heory.shiftFunctor (CochainComplex C Int) n).obj K).d i j = n.negOnePow • K.d _ 
_
参数：K : CochainComplex C Int；n i j : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma shiftFunctor_obj_d' (K : CochainComplex C ℤ) (n i j : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).obj K).d i j =
      n.negOnePow • K.d _ _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CochainComplex.shiftFunctorAdd_inv_app_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex`。
形式化陈述：shiftFunctorAdd_inv_app_f (K : CochainComplex C Int) (a b n : Int) : ((shi
ftFunctorAdd (CochainComplex C Int) a b).inv.app K).f n = (K.XIsoOfEq (by dsimp;
 rw [add_comm a, add_assoc])).hom
参数：K : CochainComplex C Int；a b n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma shiftFunctorAdd_inv_app_f (K : CochainComplex C ℤ) (a b n : ℤ) :
    ((shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_comm a, add_assoc])).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CochainComplex.shiftFunctorAdd_hom_app_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex`。
形式化陈述：shiftFunctorAdd_hom_app_f (K : CochainComplex C Int) (a b n : Int) : ((shi
ftFunctorAdd (CochainComplex C Int) a b).hom.app K).f n = (K.XIsoOfEq (by dsimp;
 rw [add_comm a, add_assoc])).hom
参数：K : CochainComplex C Int；a b n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma shiftFunctorAdd_hom_app_f (K : CochainComplex C ℤ) (a b n : ℤ) :
    ((shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_comm a, add_assoc])).hom := by
  tauto
/-
**CochainComplex.shiftFunctorAdd'_inv_app_f'** 是 Mathlib 中的一个定理，位于命名空间 `CochainC
omplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   (K : CochainComplex C ℤ) (a b ab : ℤ) (h : a + b = ab) 
(n : ℤ),   ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b ab h).inv.
app K).f n =     (HomologicalComplex.XIsoOfEq K ⋯).hom
参数：K : CochainComplex C ℤ；a b ab : ℤ；h : a + b = ab；n : ℤ；(CategoryTheory.shiftF
unctorAdd' (CochainComplex C ℤ) a b ab h).inv.app K；HomologicalComplex.XIsoOfEq 
K ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd`：∀ (C : Type u) {A : 
Type u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [in
st_2 : CategoryTheory.HasShift C A] (i j…
· 使用引理 `CochainComplex.shiftFunctorAdd_inv_app_f`：shiftFunctorAdd_inv_app_f (K :
 CochainComplex C Int) (a b n : Int) : ((shiftFunctorAdd (CochainComplex C Int) 
a b).inv.app K).f n = (K.XIsoO…
-/
lemma shiftFunctorAdd'_inv_app_f' (K : CochainComplex C ℤ) (a b ab : ℤ) (h : a + b = ab) (n : ℤ) :
    ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b ab h).inv.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [← h, add_assoc, add_comm a])).hom := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd_inv_app_f]
/-
**CochainComplex.shiftFunctorAdd'_hom_app_f'** 是 Mathlib 中的一个定理，位于命名空间 `CochainC
omplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   (K : CochainComplex C ℤ) (a b ab : ℤ) (h : a + b = ab) 
(n : ℤ),   ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b ab h).hom.
app K).f n =     (HomologicalComplex.XIsoOfEq K ⋯).hom
参数：K : CochainComplex C ℤ；a b ab : ℤ；h : a + b = ab；n : ℤ；(CategoryTheory.shiftF
unctorAdd' (CochainComplex C ℤ) a b ab h).hom.app K；HomologicalComplex.XIsoOfEq 
K ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd`：∀ (C : Type u) {A : 
Type u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [in
st_2 : CategoryTheory.HasShift C A] (i j…
· 使用引理 `CochainComplex.shiftFunctorAdd_hom_app_f`：shiftFunctorAdd_hom_app_f (K :
 CochainComplex C Int) (a b n : Int) : ((shiftFunctorAdd (CochainComplex C Int) 
a b).hom.app K).f n = (K.XIsoO…
-/
lemma shiftFunctorAdd'_hom_app_f' (K : CochainComplex C ℤ) (a b ab : ℤ) (h : a + b = ab) (n : ℤ) :
    ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b ab h).hom.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [← h, add_assoc, add_comm a])).hom := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd_hom_app_f]
/-
**CochainComplex.shiftFunctorZero_inv_app_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex`。
形式化陈述：shiftFunctorZero_inv_app_f (K : CochainComplex C Int) (n : Int) : ((Catego
ryTheory.shiftFunctorZero (CochainComplex C Int) Int).inv.app K).f n = (K.XIsoOf
Eq (by dsimp; rw [add_zero])).hom
参数：K : CochainComplex C Int；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma shiftFunctorZero_inv_app_f (K : CochainComplex C ℤ) (n : ℤ) :
    ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_zero])).hom := rfl
/-
**CochainComplex.shiftFunctorZero_hom_app_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex`。
形式化陈述：shiftFunctorZero_hom_app_f (K : CochainComplex C Int) (n : Int) : ((Catego
ryTheory.shiftFunctorZero (CochainComplex C Int) Int).hom.app K).f n = (K.XIsoOf
Eq (by dsimp; rw [add_zero])).hom
参数：K : CochainComplex C Int；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma shiftFunctorZero_hom_app_f (K : CochainComplex C ℤ) (n : ℤ) :
    ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_zero])).hom := by
  tauto
/-
**CochainComplex.XIsoOfEq_shift** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：XIsoOfEq_shift (K : CochainComplex C Int) (n : Int) {p q : Int} (hpq : p =
 q) : (K⟦n⟧).XIsoOfEq hpq = K.XIsoOfEq (show p + n = q + n by rw [hpq])
参数：K : CochainComplex C Int；n : Int；hpq : p = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma XIsoOfEq_shift (K : CochainComplex C ℤ) (n : ℤ) {p q : ℤ} (hpq : p = q) :
    (K⟦n⟧).XIsoOfEq hpq = K.XIsoOfEq (show p + n = q + n by rw [hpq]) := rfl

variable (C)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CochainComplex.shiftFunctorAdd'_eq** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] (a b c : ℤ)   (h : a + b = c),   CategoryTheory.shiftFunc
torAdd' (CochainComplex C ℤ) a b c h = CochainComplex.shiftFunctorAdd' C a b c h
参数：C : Type u；a b c : ℤ；h : a + b = c；CochainComplex C ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.shiftFunctorAdd'_hom_app_f'`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   (K : Coch
ainComplex C ℤ) (a b ab : ℤ) (h …
· 使用定理 `CochainComplex.shiftFunctorAdd'_hom_app_f`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (n₁ n₂ n₁₂ :
 ℤ)   (h : n₁ + n₂ = n₁₂) (X : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftFunctorAdd'_eq (a b c : ℤ) (h : a + b = c) :
    CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b c h =
      shiftFunctorAdd' C a b c h := by
  ext
  simp only [shiftFunctorAdd'_hom_app_f', XIsoOfEq, eqToIso.hom, shiftFunctorAdd'_hom_app_f]
/-
**CochainComplex.shiftFunctorAdd_eq** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：shiftFunctorAdd_eq (a b : Int) : CategoryTheory.shiftFunctorAdd (CochainCo
mplex C Int) a b = shiftFunctorAdd' C a b _ rfl
参数：a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd`：∀ (C : Type u) {A : 
Type u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [in
st_2 : CategoryTheory.HasShift C A] (i j…
· 使用定理 `CochainComplex.shiftFunctorAdd'_eq`：∀ (C : Type u) [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (a b c : ℤ)   (h : 
a + b = c),   CategoryTh…
-/
lemma shiftFunctorAdd_eq (a b : ℤ) :
    CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b = shiftFunctorAdd' C a b _ rfl := by
  rw [← CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd'_eq]
/-
**CochainComplex.shiftFunctorZero_eq** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：shiftFunctorZero_eq : CategoryTheory.shiftFunctorZero (CochainComplex C In
t) Int = shiftFunctorZero' C 0 rfl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.shiftFunctorZero_hom_app_f`：shiftFunctorZero_hom_app_f (K
 : CochainComplex C Int) (n : Int) : ((CategoryTheory.shiftFunctorZero (CochainC
omplex C Int) Int).hom.app K).f…
· 使用定理 `CochainComplex.shiftFunctorZero'_hom_app_f`：∀ (C : Type u) [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (n : ℤ) (h 
: n = 0)   (X : CochainComplex C…
-/
lemma shiftFunctorZero_eq :
    CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ = shiftFunctorZero' C 0 rfl := by
  ext
  rw [shiftFunctorZero_hom_app_f, shiftFunctorZero'_hom_app_f]

variable {C}

set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.shiftFunctorComm_hom_app_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex`。
形式化陈述：shiftFunctorComm_hom_app_f (K : CochainComplex C Int) (a b p : Int) : ((sh
iftFunctorComm (CochainComplex C Int) a b).hom.app K).f p = (K.XIsoOfEq (show p 
+ b + a = p + a + b by rw [add_assoc, add_comm b, add_assoc])).hom
参数：K : CochainComplex C Int；a b p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.shiftFunctorComm_eq`：shiftFunctorComm_eq (i j k : A) (h :
 i + j = k) : shiftFunctorComm C i j = (shiftFunctorAdd' C i j k h).symm ≪≫ shif
tFunctorAdd' C j i k (by…
· 使用定理 `CochainComplex.shiftFunctorAdd'_inv_app_f'`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   (K : Coch
ainComplex C ℤ) (a b ab : ℤ) (h …
· 使用定理 `CochainComplex.shiftFunctorAdd'_hom_app_f'`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   (K : Coch
ainComplex C ℤ) (a b ab : ℤ) (h …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftFunctorComm_hom_app_f (K : CochainComplex C ℤ) (a b p : ℤ) :
    ((shiftFunctorComm (CochainComplex C ℤ) a b).hom.app K).f p =
      (K.XIsoOfEq (show p + b + a = p + a + b
        by rw [add_assoc, add_comm b, add_assoc])).hom := by
  rw [shiftFunctorComm_eq _ _ _ _ rfl]
  dsimp
  rw [shiftFunctorAdd'_inv_app_f', shiftFunctorAdd'_hom_app_f']
  simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans]

variable (C)

attribute [local simp] XIsoOfEq_hom_naturality

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Shifting cochain complexes by `n` and evaluating in a degree `i` identifies
to the evaluation in degree `i'` when `n + i = i'`. -/
@[simps!]
/-
**CochainComplex.shiftEval** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：shiftEval (n i i' : Int) (hi : n + i = i') : (CategoryTheory.shiftFunctor 
(CochainComplex C Int) n) ⋙ HomologicalComplex.eval C (ComplexShape.up Int) i ≅ 
HomologicalComplex.eval C (ComplexShape.up Int) i'
参数：n i i' : Int；hi : n + i = i'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shifting cochain complexes by `n` and evaluating in a degree `i` identifies
to the evaluation in degree `i'` when `n + i = i'`.
-/
def shiftEval (n i i' : ℤ) (hi : n + i = i') :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) n) ⋙
      HomologicalComplex.eval C (ComplexShape.up ℤ) i ≅
      HomologicalComplex.eval C (ComplexShape.up ℤ) i' :=
  NatIso.ofComponents (fun K => K.XIsoOfEq (by dsimp; rw [← hi, add_comm i]))
    (by simp)

end CochainComplex

namespace CategoryTheory

open Category

namespace Functor

variable {C}
variable (F : C ⥤ D) [F.Additive]

attribute [local simp] Functor.map_zsmul

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The commutation with the shift isomorphism for the functor on cochain complexes
induced by an additive functor between preadditive categories. -/
@[simps!]
/-
**CategoryTheory.Functor.mapCochainComplexShiftIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：mapCochainComplexShiftIso (n : Int) : shiftFunctor _ n ⋙ F.mapHomologicalC
omplex (ComplexShape.up Int) ≅ F.mapHomologicalComplex (ComplexShape.up Int) ⋙ s
hiftFunctor _ n
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The commutation with the shift isomorphism for the functor on cochain complexes
induced by an additive functor between preadditive categories.
-/
def mapCochainComplexShiftIso (n : ℤ) :
    shiftFunctor _ n ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ shiftFunctor _ n :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (fun _ => by ext; dsimp; rw [id_comp, comp_id])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.commShiftMapCochainComplex** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：commShiftMapCochainComplex : (F.mapHomologicalComplex (ComplexShape.up Int
)).CommShift Int where commShiftIso
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
instance commShiftMapCochainComplex :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).CommShift ℤ where
  commShiftIso := F.mapCochainComplexShiftIso
  commShiftIso_zero := by
    ext
    rw [CommShift.isoZero_hom_app]
    dsimp
    simp only [CochainComplex.shiftFunctorZero_inv_app_f, CochainComplex.shiftFunctorZero_hom_app_f,
       HomologicalComplex.XIsoOfEq, eqToIso, eqToHom_map, eqToHom_trans, eqToHom_refl]
  commShiftIso_add := fun a b => by
    ext
    rw [CommShift.isoAdd_hom_app]
    dsimp
    rw [id_comp, id_comp]
    simp only [CochainComplex.shiftFunctorAdd_hom_app_f,
      CochainComplex.shiftFunctorAdd_inv_app_f, HomologicalComplex.XIsoOfEq, eqToIso,
      eqToHom_map, eqToHom_trans, eqToHom_refl]
/-
**CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_eq** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mapHomologicalComplex_commShiftIso_eq (n : Int) : (F.mapHomologicalComplex
 (ComplexShape.up Int)).commShiftIso n = F.mapCochainComplexShiftIso n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma mapHomologicalComplex_commShiftIso_eq (n : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n =
      F.mapCochainComplexShiftIso n := rfl

@[simp]
/-
**CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_hom_app_f** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mapHomologicalComplex_commShiftIso_hom_app_f (K : CochainComplex C Int) (n
 i : Int) : (((F.mapHomologicalComplex (ComplexShape.up Int)).commShiftIso n).ho
m.app K).f i = 𝟙 _
参数：K : CochainComplex C Int；n i : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma mapHomologicalComplex_commShiftIso_hom_app_f (K : CochainComplex C ℤ) (n i : ℤ) :
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app K).f i = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_inv_app_f** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mapHomologicalComplex_commShiftIso_inv_app_f (K : CochainComplex C Int) (n
 i : Int) : (((F.mapHomologicalComplex (ComplexShape.up Int)).commShiftIso n).in
v.app K).f i = 𝟙 _
参数：K : CochainComplex C Int；n i : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma mapHomologicalComplex_commShiftIso_inv_app_f (K : CochainComplex C ℤ) (n i : ℤ) :
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).inv.app K).f i = 𝟙 _ := rfl

end Functor

end CategoryTheory

namespace Homotopy

variable {C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `h : Homotopy φ₁ φ₂` and `n : ℤ`, this is the induced homotopy
between `φ₁⟦n⟧'` and `φ₂⟦n⟧'`. -/
/-
**Homotopy.shift** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：shift {K L : CochainComplex C Int} {φ₁ φ₂ : K ⟶ L} (h : Homotopy φ₁ φ₂) (n
 : Int) : Homotopy (φ₁⟦n⟧') (φ₂⟦n⟧') where hom _ _
参数：h : Homotopy φ₁ φ₂；n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `h : Homotopy φ₁ φ₂` and `n : ℤ`, this is the induced homotopy
between `φ₁⟦n⟧'` and `φ₂⟦n⟧'`.
-/
def shift {K L : CochainComplex C ℤ} {φ₁ φ₂ : K ⟶ L} (h : Homotopy φ₁ φ₂) (n : ℤ) :
    Homotopy (φ₁⟦n⟧') (φ₂⟦n⟧') where
  hom _ _ := n.negOnePow • h.hom _ _
  zero i j hij := by
    dsimp
    rw [h.zero, smul_zero]
    intro hij'
    dsimp at hij hij'
    lia
  comm := fun i => by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
    dsimp
    simpa only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
      Int.units_mul_self, one_smul,
      dNext_eq _ (show (ComplexShape.up ℤ).Rel (i + n) (i + 1 + n) by dsimp; lia),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1 + n) (i + n) by dsimp; lia)]
        using h.comm (i + n)

end Homotopy

namespace HomotopyCategory

/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (homotopic C (ComplexShape.up ℤ)).IsCompatibleWithShift ℤ :=
  ⟨fun n _ _ _ _ ⟨h⟩ => ⟨h.shift n⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopyCategory.hasShift** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
形式化陈述：hasShift : HasShift (HomotopyCategory C (ComplexShape.up Int)) Int
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopyCategory.instIsCompatibleWithShiftHomologicalComplexIntUpHomotop
ic`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryT
heory.Preadditive C],   (homotopic C (ComplexShape.up ℤ)).IsComp…
-/
noncomputable instance hasShift :
    HasShift (HomotopyCategory C (ComplexShape.up ℤ)) ℤ := by
  dsimp only [HomotopyCategory]
  infer_instance

variable {C} in
/-
**HomotopyCategory.shift_quotient_obj** 是 Mathlib 中的一个引理，位于命名空间 `HomotopyCategor
y`。
形式化陈述：shift_quotient_obj (K : HomologicalComplex C (.up Int)) (n : Int) : ((Homo
topyCategory.quotient _ _).obj K)⟦n⟧ = (HomotopyCategory.quotient _ _).obj (K⟦n⟧
)
参数：K : HomologicalComplex C (.up Int)；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.Quotient.functor_obj_shift`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] (r : HomRel C) (A : Type w) [inst_1 : AddMonoid A]  
 [inst_2 : CategoryTheory.HasSh…
· 使用定理 `HomotopyCategory.instIsCompatibleWithShiftHomologicalComplexIntUpHomotop
ic`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryT
heory.Preadditive C],   (homotopic C (ComplexShape.up ℤ)).IsComp…
-/
lemma shift_quotient_obj (K : HomologicalComplex C (.up ℤ)) (n : ℤ) :
    ((HomotopyCategory.quotient _ _).obj K)⟦n⟧ =
    (HomotopyCategory.quotient _ _).obj (K⟦n⟧) :=
  Quotient.functor_obj_shift ..
/-
**HomotopyCategory.commShiftQuotient** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory
`。
形式化陈述：commShiftQuotient : (HomotopyCategory.quotient C (ComplexShape.up Int)).Co
mmShift Int
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopyCategory.instIsCompatibleWithShiftHomologicalComplexIntUpHomotop
ic`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryT
heory.Preadditive C],   (homotopic C (ComplexShape.up ℤ)).IsComp…
-/
noncomputable instance commShiftQuotient :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).CommShift ℤ :=
  Quotient.functor_commShift (homotopic C (ComplexShape.up ℤ)) ℤ
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n).Additive := by
  have : ((quotient C (ComplexShape.up ℤ) ⋙ shiftFunctor _ n)).Additive :=
    Functor.additive_of_iso ((quotient C (ComplexShape.up ℤ)).commShiftIso n)
  apply Functor.additive_of_full_essSurj_comp (quotient _ _)

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [Ring R] [CategoryTheory.Linear R C] (n : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n).Linear R where
  map_smul := by
    rintro ⟨X⟩ ⟨Y⟩ f r
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective f
    have h₁ := NatIso.naturality_1 ((HomotopyCategory.quotient _ _).commShiftIso n) f
    have h₂ := NatIso.naturality_1 ((HomotopyCategory.quotient _ _).commShiftIso n) (r • f)
    dsimp at h₁ h₂
    rw [← Functor.map_smul, ← h₁, ← h₂]
    simp

section

variable {C}
variable (F : C ⥤ D) [F.Additive]

/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (F.mapHomotopyCategory (ComplexShape.up ℤ)).CommShift ℤ :=
  Quotient.liftCommShift _ _ _ _
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatTrans.CommShift (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom ℤ :=
  Quotient.liftCommShift_compatibility _ _ _ _

end

end HomotopyCategory

