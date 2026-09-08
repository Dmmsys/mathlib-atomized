/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.InducedShiftSequence
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Compatibilities of the homology functor with the shift

This file studies how homology of cochain complexes behaves with respect to
the shift: there is a natural isomorphism `(K⟦n⟧).homology a ≅ K.homology a`
when `n + a = a'`. This is summarized by instances
`(homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ` in the `CochainComplex`
and `HomotopyCategory` namespaces.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category ComplexShape Limits

variable (C : Type*) [Category* C] [Preadditive C]

namespace CochainComplex

open HomologicalComplex

attribute [local simp] XIsoOfEq_hom_naturality smul_smul

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `(K⟦n⟧).sc' i j k ≅ K.sc' i' j' k'` when `n + i = i'`,
`n + j = j'` and `n + k = k'`. -/
@[simps!]
/-
**CochainComplex.shiftShortComplexFunctor'** 是 Mathlib 中的一个定义，位于命名空间 `CochainCom
plex`。
形式化陈述：shiftShortComplexFunctor' (n i j k i' j' k' : Int) (hi : n + i = i') (hj :
 n + j = j') (hk : n + k = k') : (CategoryTheory.shiftFunctor (CochainComplex C 
Int) n) ⋙ shortComplexFunctor' C _ i j k ≅ shortComplexFunctor' C _ i' j' k'
参数：n i j k i' j' k' : Int；hi : n + i = i'；hj : n + j = j'；hk : n + k = k'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `(K⟦n⟧).sc' i j k ≅ K.sc' i' j' k'` when `n + i = i'`,
`n + j = j'` and `n + k = k'`.
-/
def shiftShortComplexFunctor' (n i j k i' j' k' : ℤ)
    (hi : n + i = i') (hj : n + j = j') (hk : n + k = k') :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) n) ⋙ shortComplexFunctor' C _ i j k ≅
      shortComplexFunctor' C _ i' j' k' :=
  NatIso.ofComponents (fun K => ShortComplex.isoMk
      (n.negOnePow • ((shiftEval C n i i' hi).app K))
      ((shiftEval C n j j' hj).app K) (n.negOnePow • ((shiftEval C n k k' hk).app K))
      (by simp) (by simp))
      (fun f ↦ by ext <;> simp)

/-- The natural isomorphism `(K⟦n⟧).sc i ≅ K.sc i'` when `n + i = i'`. -/
@[simps!]
/-
**CochainComplex.shiftShortComplexFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `CochainC
omplex`。
形式化陈述：shiftShortComplexFunctorIso (n i i' : Int) (hi : n + i = i') : shiftFuncto
r C n ⋙ shortComplexFunctor C _ i ≅ shortComplexFunctor C _ i'
参数：n i i' : Int；hi : n + i = i'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `(K⟦n⟧).sc i ≅ K.sc i'` when `n + i = i'`.
-/
noncomputable def shiftShortComplexFunctorIso (n i i' : ℤ) (hi : n + i = i') :
    shiftFunctor C n ⋙ shortComplexFunctor C _ i ≅ shortComplexFunctor C _ i' :=
  shiftShortComplexFunctor' C n _ i _ _ i' _
    (by simp only [prev]; lia) hi (by simp only [next]; lia)

variable {C}

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.shiftShortComplexFunctorIso_zero_add_hom_app** 是 Mathlib 中的一个引理
，位于命名空间 `CochainComplex`。
形式化陈述：shiftShortComplexFunctorIso_zero_add_hom_app (a : Int) (K : CochainComplex
 C Int) : (shiftShortComplexFunctorIso C 0 a a (zero_add a)).hom.app K = (shortC
omplexFunctor C (ComplexShape.up Int) a).map ((shiftFunctorZero (CochainComplex 
C Int) Int).hom.app K)
参数：a : Int；K : CochainComplex C Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.hom_ext`：hom_ext (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ 
= g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₁`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditi
ve C] (n i i' : ℤ)   (hi : n + i = i') (X :…
· 使用定理 `CochainComplex.shiftEval_hom_app`：∀ (C : Type u) [inst : CategoryTheory.
Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (n i i' : ℤ)   (hi : 
n + i = i') (X : Cocha…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `HomologicalComplex.shortComplexFunctor_map_τ₁`：∀ (C : Type u_1) [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {ι : Type u_2} (c : Com…
· 使用引理 `CochainComplex.shiftFunctorZero_hom_app_f`：shiftFunctorZero_hom_app_f (K
 : CochainComplex C Int) (n : Int) : ((CategoryTheory.shiftFunctorZero (CochainC
omplex C Int) Int).hom.app K).f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₂`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditi
ve C] (n i i' : ℤ)   (hi : n + i = i') (X :…
· 使用定理 `HomologicalComplex.shortComplexFunctor_map_τ₂`：∀ (C : Type u_1) [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {ι : Type u_2} (c : Com…
· 使用定理 `CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₃`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditi
ve C] (n i i' : ℤ)   (hi : n + i = i') (X :…
· 使用定理 `HomologicalComplex.shortComplexFunctor_map_τ₃`：∀ (C : Type u_1) [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {ι : Type u_2} (c : Com…
-/
lemma shiftShortComplexFunctorIso_zero_add_hom_app (a : ℤ) (K : CochainComplex C ℤ) :
    (shiftShortComplexFunctorIso C 0 a a (zero_add a)).hom.app K =
      (shortComplexFunctor C (ComplexShape.up ℤ) a).map
        ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K) := by
  ext <;> simp [one_smul, shiftFunctorZero_hom_app_f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.shiftShortComplexFunctorIso_add'_hom_app** 是 Mathlib 中的一个定理，位于命
名空间 `CochainComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C] (n m mn : ℤ)   (hmn : m + n = mn) (a a' a'' : ℤ) (h
a' : n + a = a') (ha'' : m + a' = a'') (K : CochainComplex C ℤ),   (CochainCompl
ex.shiftShortComplexFunctorIso C mn a a'' ⋯).hom.app K =     CategoryTheory.Cate
goryStruct.comp       ((HomologicalComplex.shortComplexFunctor C (ComplexShape.u
p ℤ) a).map         ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) m n m
n hmn).hom.app K))       (CategoryTheory.CategoryStruct.comp         ((CochainCo
mplex.shiftShortComplexFunctorIso C n a a' ha').hom.app           ((CategoryTheo
ry.shiftFunctor (CochainComplex C ℤ) m).obj K))         ((CochainComplex.shiftSh
ortComplexFunctorIso C m a' a'' ha'').hom.app K))
参数：n m mn : ℤ；hmn : m + n = mn；a a' a'' : ℤ；ha' : n + a = a'；ha'' : m + a' = a''
；K : CochainComplex C ℤ；CochainComplex.shiftShortComplexFunctorIso C mn a a'' ⋯；
(HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) a).map         ((C
ategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) m n mn hmn).hom.app K)；Categ
oryTheory.CategoryStruct.comp         ((CochainComplex.shiftShortComplexFunctorI
so C n a a' ha').hom.app           ((CategoryTheory.shiftFunctor (CochainComplex
 C ℤ) m).obj K))         ((CochainComplex.shiftShortComplexFunctorIso C m a' a''
 ha'').hom.app K)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.hom_ext`：hom_ext (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ 
= g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.negOnePow_add`：negOnePow_add (n₁ n₂ : Int) : (n₁ + n₂).negOnePow = n
₁.negOnePow * n₂.negOnePow
· 使用定理 `CochainComplex.shiftFunctorAdd'_hom_app_f'`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   (K : Coch
ainComplex C ℤ) (a b ab : ℤ) (h …
· 使用引理 `CategoryTheory.Linear.comp_units_smul`：comp_units_smul {X Y Z : C} (f : 
X ⟶ Y) (r : Rˣ) (g : Y ⟶ Z) : f ≫ (r • g) = r • f ≫ g
· 使用引理 `CategoryTheory.Linear.units_smul_comp`：units_smul_comp {X Y Z : C} (r : 
Rˣ) (f : X ⟶ Y) (g : Y ⟶ Z) : (r • f) ≫ g = r • f ≫ g
· 使用引理 `HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom`：XIsoOfEq_hom_comp_XIs
oOfEq_hom (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι} (h₁₂ : p₁ = p₂) (h₂₃ : p₂ 
= p₃) : (K.XIsoOfEq h₁₂).hom ≫ (K.XIsoO…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftShortComplexFunctorIso_add'_hom_app
    (n m mn : ℤ) (hmn : m + n = mn) (a a' a'' : ℤ) (ha' : n + a = a') (ha'' : m + a' = a'')
    (K : CochainComplex C ℤ) :
    (shiftShortComplexFunctorIso C mn a a'' (by rw [← ha'', ← ha', ← add_assoc, hmn])).hom.app K =
      (shortComplexFunctor C (ComplexShape.up ℤ) a).map
        ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) m n mn hmn).hom.app K) ≫
        (shiftShortComplexFunctorIso C n a a' ha').hom.app (K⟦m⟧) ≫
        (shiftShortComplexFunctorIso C m a' a'' ha'').hom.app K := by
  ext <;> dsimp <;> simp only [← hmn, Int.negOnePow_add, shiftFunctorAdd'_hom_app_f',
    XIsoOfEq_shift, Linear.comp_units_smul, Linear.units_smul_comp,
    XIsoOfEq_hom_comp_XIsoOfEq_hom, smul_smul]

variable [CategoryWithHomology C]

namespace ShiftSequence

variable (C) in
/-- The natural isomorphism `(K⟦n⟧).homology a ≅ K.homology a'` when `n + a = a'`. -/
/-
**CochainComplex.ShiftSequence.shiftIso** 是 Mathlib 中的一个定义，位于命名空间 `CochainComple
x.ShiftSequence`。
形式化陈述：shiftIso (n a a' : Int) (ha' : n + a = a') : (CategoryTheory.shiftFunctor 
_ n) ⋙ homologyFunctor C (ComplexShape.up Int) a ≅ homologyFunctor C (ComplexSha
pe.up Int) a'
参数：n a a' : Int；ha' : n + a = a'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `(K⟦n⟧).homology a ≅ K.homology a'` when `n + a = a'`.
-/
noncomputable def shiftIso (n a a' : ℤ) (ha' : n + a = a') :
    (CategoryTheory.shiftFunctor _ n) ⋙ homologyFunctor C (ComplexShape.up ℤ) a ≅
      homologyFunctor C (ComplexShape.up ℤ) a' :=
  Functor.isoWhiskerLeft _ (homologyFunctorIso C (ComplexShape.up ℤ) a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (shiftShortComplexFunctorIso C n a a' ha')
      (ShortComplex.homologyFunctor C) ≪≫
    (homologyFunctorIso C (ComplexShape.up ℤ) a').symm

set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.ShiftSequence.shiftIso_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Cocha
inComplex.ShiftSequence`。
形式化陈述：shiftIso_hom_app (n a a' : Int) (ha' : n + a = a') (K : CochainComplex C I
nt) : (shiftIso C n a a' ha').hom.app K = ShortComplex.homologyMap ((shiftShortC
omplexFunctorIso C n a a' ha').hom.app K)
参数：n a a' : Int；ha' : n + a = a'；K : CochainComplex C Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
lemma shiftIso_hom_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
    (shiftIso C n a a' ha').hom.app K =
      ShortComplex.homologyMap ((shiftShortComplexFunctorIso C n a a' ha').hom.app K) := by
  simp [shiftIso, HomologicalComplex.homology]

set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.ShiftSequence.shiftIso_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `Cocha
inComplex.ShiftSequence`。
形式化陈述：shiftIso_inv_app (n a a' : Int) (ha' : n + a = a') (K : CochainComplex C I
nt) : (shiftIso C n a a' ha').inv.app K = ShortComplex.homologyMap ((shiftShortC
omplexFunctorIso C n a a' ha').inv.app K)
参数：n a a' : Int；ha' : n + a = a'；K : CochainComplex C Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftIso_inv_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
    (shiftIso C n a a' ha').inv.app K =
      ShortComplex.homologyMap ((shiftShortComplexFunctorIso C n a a' ha').inv.app K) := by
  simp [shiftIso, HomologicalComplex.homology]

end ShiftSequence

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance :
    (homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ where
  sequence n := homologyFunctor C (ComplexShape.up ℤ) n
  isoZero := Iso.refl _
  shiftIso n a a' ha' := ShiftSequence.shiftIso C n a a' ha'
  shiftIso_zero a := by
    ext K
    dsimp [homologyMap]
    simp only [ShiftSequence.shiftIso_hom_app, comp_id,
      shiftShortComplexFunctorIso_zero_add_hom_app]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext K
    dsimp [homologyMap]
    simp only [ShiftSequence.shiftIso_hom_app, id_comp,
      ← ShortComplex.homologyMap_comp, shiftFunctorAdd'_eq_shiftFunctorAdd,
      shiftShortComplexFunctorIso_add'_hom_app n m _ rfl a a' a'' ha' ha'' K]
/-
**CochainComplex.quasiIsoAt_shift_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`
。
形式化陈述：quasiIsoAt_shift_iff {K L : CochainComplex C Int} (φ : K ⟶ L) (n i j : Int
) (h : n + i = j) : QuasiIsoAt (φ⟦n⟧') i ↔ QuasiIsoAt φ j
参数：φ : K ⟶ L；n i j : Int；h : n + i = j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatIso.isIso_map_iff`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F₁ F₂ : CategoryT…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
lemma quasiIsoAt_shift_iff {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n i j : ℤ) (h : n + i = j) :
    QuasiIsoAt (φ⟦n⟧') i ↔ QuasiIsoAt φ j := by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (NatIso.isIso_map_iff
    ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso n i j h) φ)
/-
**CochainComplex.quasiIso_shift_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：quasiIso_shift_iff {K L : CochainComplex C Int} (φ : K ⟶ L) (n : Int) : Qu
asiIso (φ⟦n⟧') ↔ QuasiIso φ
参数：φ : K ⟶ L；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `CochainComplex.quasiIsoAt_shift_iff`：quasiIsoAt_shift_iff {K L : Cochain
Complex C Int} (φ : K ⟶ L) (n i j : Int) (h : n + i = j) : QuasiIsoAt (φ⟦n⟧') i 
↔ QuasiIsoAt φ j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma quasiIso_shift_iff {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) :
    QuasiIso (φ⟦n⟧') ↔ QuasiIso φ := by
  simp only [quasiIso_iff, fun i ↦ quasiIsoAt_shift_iff φ n i _ rfl]
  constructor
  · intro h j
    obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by lia⟩
    exact h i
  · intro h i
    exact h (n + i)
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) [QuasiIso φ] :
    QuasiIso (φ⟦n⟧') := by
  rw [quasiIso_shift_iff]
  infer_instance
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).IsCompatibleWithShift ℤ where
  condition n := by ext; apply quasiIso_shift_iff

variable (C) in
/-
**CochainComplex.homologyFunctor_shift** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex
`。
形式化陈述：homologyFunctor_shift (n : Int) : (homologyFunctor C (ComplexShape.up Int)
 0).shift n = homologyFunctor C (ComplexShape.up Int) n
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
-/
lemma homologyFunctor_shift (n : ℤ) :
    (homologyFunctor C (ComplexShape.up ℤ) 0).shift n =
      homologyFunctor C (ComplexShape.up ℤ) n := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CochainComplex.liftCycles_shift_homology** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftCycles_shift_homologyπ
    (K : CochainComplex C ℤ) {A : C} {n i : ℤ} (f : A ⟶ (K⟦n⟧).X i) (j : ℤ)
    (hj : (up ℤ).next i = j) (hf : f ≫ (K⟦n⟧).d i j = 0) (i' : ℤ) (hi' : n + i = i') (j' : ℤ)
    (hj' : (up ℤ).next i' = j') :
    (K⟦n⟧).liftCycles f j hj hf ≫ (K⟦n⟧).homologyπ i =
      K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' (by lia)).hom) j' hj' (by
        simp only [next] at hj hj'
        obtain rfl : i' = i + n := by lia
        obtain rfl : j' = j + n := by lia
        dsimp at hf ⊢
        simp only [Linear.comp_units_smul] at hf
        apply (one_smul (M := ℤˣ) _).symm.trans _
        rw [← Int.units_mul_self n.negOnePow, mul_smul, comp_id, hf, smul_zero]) ≫
        K.homologyπ i' ≫
          ((HomologicalComplex.homologyFunctor C (up ℤ) 0).shiftIso n i i' hi').inv.app K := by
  simp only [liftCycles, homologyπ,
    shiftFunctorObjXIso, Functor.shiftIso, Functor.ShiftSequence.shiftIso,
    ShiftSequence.shiftIso_inv_app, ShortComplex.homologyπ_naturality,
    ShortComplex.liftCycles_comp_cyclesMap_assoc, shiftShortComplexFunctorIso_inv_app_τ₂,
    assoc, Iso.hom_inv_id, comp_id]
  rfl

end CochainComplex

namespace HomotopyCategory

variable [CategoryWithHomology C]

/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance :
    (homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.induced (homologyFunctorFactors C (ComplexShape.up ℤ) 0) ℤ
    (homologyFunctor C (ComplexShape.up ℤ))
    (homologyFunctorFactors C (ComplexShape.up ℤ))

variable {C}
/-
**HomotopyCategory.homologyShiftIso_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `HomotopyC
ategory`。
形式化陈述：homologyShiftIso_hom_app (n a a' : Int) (ha' : n + a = a') (K : CochainCom
plex C Int) : ((homologyFunctor C (ComplexShape.up Int) 0).shiftIso n a a' ha').
hom.app ((quotient _ _).obj K) = (homologyFunctor _ _ a).map (((quotient _ _).co
mmShiftIso n).inv.app K) ≫ (homologyFunctorFactors _ _ a).hom.app (K⟦n⟧) ≫ ((Hom
ologicalComplex.homologyFunctor _ _ 0).shiftIso n a a' ha').hom.app K ≫ (homolog
yFunctorFactors _ _ a').inv.app K
参数：n a a' : Int；ha' : n + a = a'；K : CochainComplex C Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ShiftSequence.induced_shiftIso_hom_app_obj`：induc
ed_shiftIso_hom_app_obj (n a a' : M) (ha' : n + a = a') (X : C) : letI
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
lemma homologyShiftIso_hom_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
    ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso n a a' ha').hom.app
      ((quotient _ _).obj K) =
    (homologyFunctor _ _ a).map (((quotient _ _).commShiftIso n).inv.app K) ≫
      (homologyFunctorFactors _ _ a).hom.app (K⟦n⟧) ≫
      ((HomologicalComplex.homologyFunctor _ _ 0).shiftIso n a a' ha').hom.app K ≫
      (homologyFunctorFactors _ _ a').inv.app K := by
  apply Functor.ShiftSequence.induced_shiftIso_hom_app_obj

@[reassoc]
/-
**HomotopyCategory.homologyFunctor_shiftMap** 是 Mathlib 中的一个引理，位于命名空间 `HomotopyC
ategory`。
形式化陈述：homologyFunctor_shiftMap {K L : CochainComplex C Int} {n : Int} (f : K ⟶ L
⟦n⟧) (a a' : Int) (h : n + a = a') : (homologyFunctor C (ComplexShape.up Int) 0)
.shiftMap (ShiftedHom.map f (quotient _ _)) a a' h = (homologyFunctorFactors _ _
 a).hom.app K ≫ (HomologicalComplex.homologyFunctor C (ComplexShape.up Int) 0).s
hiftMap f a a' h ≫ (homologyFunctorFactors _ _ a').inv.app L
参数：f : K ⟶ L⟦n⟧；a a' : Int；h : n + a = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CategoryTheory.Functor.ShiftSequence.induced_shiftMap`：induced_shiftMap 
{n : M} {X Y : C} (f : X ⟶ Y⟦n⟧) (a a' : M) (h : n + a = a') : letI
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
lemma homologyFunctor_shiftMap
    {K L : CochainComplex C ℤ} {n : ℤ} (f : K ⟶ L⟦n⟧) (a a' : ℤ) (h : n + a = a') :
    (homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (ShiftedHom.map f (quotient _ _)) a a' h =
        (homologyFunctorFactors _ _ a).hom.app K ≫
          (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap f a a' h ≫
            (homologyFunctorFactors _ _ a').inv.app L := by
  apply Functor.ShiftSequence.induced_shiftMap

end HomotopyCategory

