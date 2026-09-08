/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# Projective resolutions as cochain complexes indexed by the integers

Given a projective resolution `R` of an object `X` in an abelian category `C`,
we define `R.cochainComplex : CochainComplex C ℤ`, which is the extension
of `R.complex : ChainComplex C ℕ`, and the quasi-isomorphism
`R.π' : R.cochainComplex ⟶ (CochainComplex.singleFunctor C 0).obj X`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace ProjectiveResolution

section

variable [HasZeroObject C] [Preadditive C] {X : C}
  (R : ProjectiveResolution X)

/-- If `R : ProjectiveResolution X`, this is the cochain complex indexed by `ℤ`
obtained by extending by zero the chain complex `R.complex` indexed by `ℕ`. -/
/-
**CategoryTheory.ProjectiveResolution.cochainComplex** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ProjectiveResolution`。
形式化陈述：cochainComplex : CochainComplex C Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R : ProjectiveResolution X`, this is the cochain complex indexed by `ℤ`
obtained by extending by zero the chain complex `R.complex` indexed by `ℕ`.
-/
noncomputable def cochainComplex : CochainComplex C ℤ :=
  R.complex.extend ComplexShape.embeddingDownNat

/-- If `R : ProjectiveResolution X`, then `R.cochainComplex.X n` (with `n : ℕ`)
is isomorphic to `R.complex.X k` (with `k : ℕ`) when `k = n`. -/
/-
**CategoryTheory.ProjectiveResolution.cochainComplexXIso** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：cochainComplexXIso (n : Int) (k : Nat) (h : -k = n
参数：n : Int；k : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R : ProjectiveResolution X`, then `R.cochainComplex.X n` (with `n : ℕ`)
is isomorphic to `R.complex.X k` (with `k : ℕ`) when `k = n`.
-/
noncomputable def cochainComplexXIso (n : ℤ) (k : ℕ) (h : -k = n := by lia) :
    R.cochainComplex.X n ≅ R.complex.X k :=
  HomologicalComplex.extendXIso _ _ h

@[reassoc]
/-
**CategoryTheory.ProjectiveResolution.cochainComplex_d** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ProjectiveResolution`。
形式化陈述：cochainComplex_d (n₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : -k₁ = n₁
参数：n₁ n₂ : Int；k₁ k₂ : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.extend_d_eq`：extend_d_eq {i' j' : ι'} {i j : ι} (hi :
 e.f i = i') (hj : e.f j = j') : (K.extend e).d i' j' = (K.extendXIso e hi).hom 
≫ K.d i j ≫ (K.exten…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma cochainComplex_d (n₁ n₂ : ℤ) (k₁ k₂ : ℕ) (h₁ : -k₁ = n₁ := by lia) (h₂ : -k₂ = n₂ := by lia) :
    R.cochainComplex.d n₁ n₂ = (cochainComplexXIso _ _ _).hom ≫
      R.complex.d k₁ k₂ ≫ (cochainComplexXIso _ _ _).inv :=
  HomologicalComplex.extend_d_eq _ _ h₁ h₂
/-
**CategoryTheory.ProjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : R.cochainComplex.IsStrictlyLE 0 := by
  dsimp [cochainComplex]
  infer_instance
/-
**CategoryTheory.ProjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : Projective (R.cochainComplex.X n) := by
  by_cases hn : n ≤ 0
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hn
    exact Projective.of_iso (R.cochainComplexXIso (-k) k).symm inferInstance
  · exact IsZero.projective (CochainComplex.isZero_of_isStrictlyLE _ 0 _)

/-- The quasi-isomorphism `R.cochainComplex ⟶ (CochainComplex.singleFunctor C 0).obj X`
in `CochainComplex C ℤ` when `R` is a projective resolution of `X`. -/
/-
**CategoryTheory.ProjectiveResolution.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quasi-isomorphism `R.cochainComplex ⟶ (CochainComplex.singleFunctor C 0).obj
 X`
in `CochainComplex C ℤ` when `R` is a projective resolution of `X`.
-/
noncomputable def π' : R.cochainComplex ⟶ (CochainComplex.singleFunctor C 0).obj X :=
    (ComplexShape.embeddingDownNat.extendFunctor C).map R.π ≫
      (HomologicalComplex.extendSingleIso _ _ _ _ (by simp)).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ProjectiveResolution.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π'_f_zero :
    R.π'.f 0 = (R.cochainComplexXIso _ _).hom ≫ R.π.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv := by
  dsimp [π']
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by simp),
    HomologicalComplex.extendSingleIso_hom_f]
  cat_disch

end

variable [Abelian C] {X : C} (R : ProjectiveResolution X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ProjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : QuasiIso R.π' := by dsimp [π']; infer_instance
/-
**CategoryTheory.ProjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : R.cochainComplex.IsGE 0 := by
  simp only [HomologicalComplex.isSupported_iff_of_quasiIso R.π']
  infer_instance

namespace Hom

variable {R} {X' : C} {R' : ProjectiveResolution X'} {f : X ⟶ X'}
  (φ : Hom R R' f)

/-- The morphism on cochain complexes indexed by `ℤ` that is induced by
a (heterogeneous) morphism of projective resolutions. -/
/-
**CategoryTheory.ProjectiveResolution.Hom.hom'** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ProjectiveResolution.Hom`。
形式化陈述：hom' : R.cochainComplex ⟶ R'.cochainComplex
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
The morphism on cochain complexes indexed by `ℤ` that is induced by
a (heterogeneous) morphism of projective resolutions.
-/
noncomputable def hom' : R.cochainComplex ⟶ R'.cochainComplex :=
  HomologicalComplex.extendMap φ.hom _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ProjectiveResolution.Hom.hom'_f** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.ProjectiveResolution.Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {X : C}   {R : CategoryTheory.ProjectiveResolution X} {X' : C
} {R' : CategoryTheory.ProjectiveResolution X'} {f : X ⟶ X'}   (φ : R.Hom R' f) 
(n : ℤ) (m : ℕ) (h : -↑m = n),   φ.hom'.f n =     CategoryTheory.CategoryStruct.
comp (R.cochainComplexXIso n m h).hom       (CategoryTheory.CategoryStruct.comp 
(φ.hom.f m) (R'.cochainComplexXIso n m h).inv)
参数：φ : R.Hom R' f；n : ℤ；m : ℕ；h : -↑m = n；R.cochainComplexXIso n m h；CategoryThe
ory.CategoryStruct.comp (φ.hom.f m) (R'.cochainComplexXIso n m h).inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.extendMap_f`：extendMap_f {i : ι} {i' : ι'} (h : e.f i
 = i') : (extendMap φ e).f i' = (extendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e
 h).inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom'_f (n : ℤ) (m : ℕ) (h : -m = n) :
    φ.hom'.f n =
    (R.cochainComplexXIso n m h).hom ≫ φ.hom.f m ≫ (R'.cochainComplexXIso n m h).inv := by
  simp [hom', HomologicalComplex.extendMap_f _
    ComplexShape.embeddingDownNat (i := m) (i' := n) (by dsimp; lia),
    cochainComplexXIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ProjectiveResolution.Hom.hom'_comp_** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ProjectiveResolution.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom'_comp_π' :
    φ.hom' ≫ R'.π' = R.π' ≫ (CochainComplex.singleFunctor C 0).map f :=
  HomologicalComplex.to_single_hom_ext (by
    simp [hom'_f _ 0 0 rfl, π'_f_zero, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors,
      HomologicalComplex.single, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq])

end Hom

end ProjectiveResolution

end CategoryTheory

