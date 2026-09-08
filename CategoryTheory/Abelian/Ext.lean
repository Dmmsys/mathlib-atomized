/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Adam Topaz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Ext

We define `Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R` for any `R`-linear abelian category `C`
by (left) deriving in the first argument of the bifunctor `(X, Y) ↦ ModuleCat.of R (unop X ⟶ Y)`.

## Implementation

TODO (@joelriou): When the derived category enters mathlib, the Ext groups shall be
redefined using morphisms in the derived category, and then it will be possible to
compute `Ext` using both projective or injective resolutions.

-/

@[expose] public section


noncomputable section

open CategoryTheory Limits

variable (R : Type*) [Ring R] (C : Type*) [Category* C] [Abelian C] [Linear R C]
  [EnoughProjectives C]

/-- `Ext R C n` is defined by deriving in
the first argument of `(X, Y) ↦ ModuleCat.of R (unop X ⟶ Y)`
(which is the second argument of `linearYoneda`).
-/
/-
**Ext** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ext (n : Nat) : Cᵒᵖ ⥤ C ⥤ ModuleCat R
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ProjectiveResolution.instHasProjectiveResolutions`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abel
ian C]   [CategoryTheory.EnoughProjectives C], Categor…

--- 原说明 ---
`Ext R C n` is defined by deriving in
the first argument of `(X, Y) ↦ ModuleCat.of R (unop X ⟶ Y)`
(which is the second argument of `linearYoneda`).
-/
def Ext (n : ℕ) : Cᵒᵖ ⥤ C ⥤ ModuleCat R :=
  Functor.flip
    { obj := fun Y => (((linearYoneda R C).obj Y).rightOp.leftDerived n).leftOp
      map := fun f => ((((linearYoneda R C).map f).rightOp).leftDerived n).leftOp }

open ZeroObject

variable {R C}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given a chain complex `X` and an object `Y`, this is the cochain complex
which in degree `i` consists of the module of morphisms `X.X i ⟶ Y`. -/
@[simps! X d]
/-
**ChainComplex.linearYonedaObj** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ChainComplex.linearYonedaObj {α : Type*} [AddRightCancelSemigroup α] [One 
α] (X : ChainComplex C α) (A : Type*) [Ring A] [Linear A C] (Y : C) : CochainCom
plex (ModuleCat A) α
参数：X : ChainComplex C α；A : Type*；Y : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
Given a chain complex `X` and an object `Y`, this is the cochain complex
which in degree `i` consists of the module of morphisms `X.X i ⟶ Y`.
-/
def ChainComplex.linearYonedaObj {α : Type*} [AddRightCancelSemigroup α] [One α]
    (X : ChainComplex C α) (A : Type*) [Ring A] [Linear A C] (Y : C) :
    CochainComplex (ModuleCat A) α :=
  ((((linearYoneda A C).obj Y).rightOp.mapHomologicalComplex _).obj X).unop

namespace CategoryTheory

namespace ProjectiveResolution

variable {X : C} (P : ProjectiveResolution X)

/-- `Ext` can be computed using a projective resolution. -/
/-
**CategoryTheory.ProjectiveResolution.isoExt** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ProjectiveResolution`。
形式化陈述：isoExt (n : Nat) (Y : C) : ((Ext R C n).obj (Opposite.op X)).obj Y ≅ (P.co
mplex.linearYonedaObj R Y).homology n
参数：n : Nat；Y : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.ProjectiveResolution.instHasProjectiveResolutions`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abel
ian C]   [CategoryTheory.EnoughProjectives C], Categor…

--- 原说明 ---
`Ext` can be computed using a projective resolution.
-/
def isoExt (n : ℕ) (Y : C) : ((Ext R C n).obj (Opposite.op X)).obj Y ≅
    (P.complex.linearYonedaObj R Y).homology n :=
  (P.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).unop.symm ≪≫
    (HomologicalComplex.homologyUnop _ _).symm

end ProjectiveResolution

end CategoryTheory

/-- If `X : C` is projective and `n : ℕ`, then `Ext^(n + 1) X Y ≅ 0` for any `Y`. -/
/-
**isZero_Ext_succ_of_projective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isZero_Ext_succ_of_projective (X Y : C) [Projective X] (n : Nat) : IsZero 
(((Ext R C (n + 1)).obj (Opposite.op X)).obj Y)
参数：X Y : C；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplex.exactAt_iff_isZero_homology`：exactAt_iff_isZero_homol
ogy [K.HasHomology i] : K.ExactAt i ↔ IsZero (K.homology i)
· 使用引理 `HomologicalComplex.exactAt_iff`：exactAt_iff : K.ExactAt i ↔ (K.sc i).Exa
ct
· 使用引理 `CategoryTheory.ShortComplex.exact_of_isZero_X₂`：exact_of_isZero_X₂ (h : 
IsZero S.X₂) : S.Exact
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `HomologicalComplex.isZero_single_obj_X`：isZero_single_obj_X (j : ι) (A :
 V) (i : ι) (hi : i != j) : IsZero (((single V c j).obj A).X i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If `X : C` is projective and `n : ℕ`, then `Ext^(n + 1) X Y ≅ 0` for any `Y`.
-/
lemma isZero_Ext_succ_of_projective (X Y : C) [Projective X] (n : ℕ) :
    IsZero (((Ext R C (n + 1)).obj (Opposite.op X)).obj Y) := by
  refine IsZero.of_iso ?_ ((ProjectiveResolution.self X).isoExt (n + 1) Y)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff]
  refine ShortComplex.exact_of_isZero_X₂ _ ?_
  rw [IsZero.iff_id_eq_zero]
  ext (x : _ ⟶ _)
  obtain rfl : x = 0 := (HomologicalComplex.isZero_single_obj_X
    (ComplexShape.down ℕ) 0 X (n + 1) (by simp)).eq_of_src _ _
  rfl
