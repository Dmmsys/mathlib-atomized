/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-!
# Injective resolutions as cochain complexes indexed by the integers

Given an injective resolution `R` of an object `X` in an abelian category `C`,
we define `R.cochainComplex : CochainComplex C ℤ`, which is the extension
of `R.cocomplex : CochainComplex C ℕ`, and the quasi-isomorphism
`R.ι' : (CochainComplex.singleFunctor C 0).obj X ⟶ R.cochainComplex`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace InjectiveResolution

section

variable [HasZeroObject C] [Preadditive C] {X : C}
  (R : InjectiveResolution X)

/-- If `R : InjectiveResolution X`, this is the cochain complex indexed by `ℤ`
obtained by extending by zero the cochain complex `R.cocomplex` indexed by `ℕ`. -/
/-
**CategoryTheory.InjectiveResolution.cochainComplex** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.InjectiveResolution`。
形式化陈述：cochainComplex : CochainComplex C Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R : InjectiveResolution X`, this is the cochain complex indexed by `ℤ`
obtained by extending by zero the cochain complex `R.cocomplex` indexed by `ℕ`.
-/
noncomputable def cochainComplex : CochainComplex C ℤ :=
  R.cocomplex.extend ComplexShape.embeddingUpNat
/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : R.cochainComplex.IsStrictlyGE 0 := by
  dsimp [cochainComplex]
  infer_instance

/-- If `R : InjectiveResolution X`, then `R.cochainComplex.X n` (with `n : ℕ`)
is isomorphic to `R.cocomplex.X k` (with `k : ℕ`) when `k = n`. -/
/-
**CategoryTheory.InjectiveResolution.cochainComplexXIso** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.InjectiveResolution`。
形式化陈述：cochainComplexXIso (n : Int) (k : Nat) (h : k = n) : R.cochainComplex.X n 
≅ R.cocomplex.X k
参数：n : Int；k : Nat；h : k = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R : InjectiveResolution X`, then `R.cochainComplex.X n` (with `n : ℕ`)
is isomorphic to `R.cocomplex.X k` (with `k : ℕ`) when `k = n`.
-/
noncomputable def cochainComplexXIso (n : ℤ) (k : ℕ) (h : k = n) :
    R.cochainComplex.X n ≅ R.cocomplex.X k :=
  HomologicalComplex.extendXIso _ _ h

@[reassoc]
/-
**CategoryTheory.InjectiveResolution.cochainComplex_d** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.InjectiveResolution`。
形式化陈述：cochainComplex_d (n₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : k₁ = n₁) (h₂ : k₂ = n₂)
 : R.cochainComplex.d n₁ n₂ = (cochainComplexXIso _ _ _ h₁).hom ≫ R.cocomplex.d 
k₁ k₂ ≫ (cochainComplexXIso _ _ _ h₂).inv
参数：n₁ n₂ : Int；k₁ k₂ : Nat；h₁ : k₁ = n₁；h₂ : k₂ = n₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.extend_d_eq`：extend_d_eq {i' j' : ι'} {i j : ι} (hi :
 e.f i = i') (hj : e.f j = j') : (K.extend e).d i' j' = (K.extendXIso e hi).hom 
≫ K.d i j ≫ (K.exten…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma cochainComplex_d (n₁ n₂ : ℤ) (k₁ k₂ : ℕ) (h₁ : k₁ = n₁) (h₂ : k₂ = n₂) :
    R.cochainComplex.d n₁ n₂ = (cochainComplexXIso _ _ _ h₁).hom ≫
      R.cocomplex.d k₁ k₂ ≫ (cochainComplexXIso _ _ _ h₂).inv :=
  HomologicalComplex.extend_d_eq _ _ h₁ h₂
/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : R.cochainComplex.IsStrictlyGE 0 := by
  dsimp [cochainComplex]
  infer_instance
/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : Injective (R.cochainComplex.X n) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact Injective.of_iso (R.cochainComplexXIso _ _ rfl).symm inferInstance
  · exact IsZero.injective (CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by lia))

/-- The quasi-isomorphism `(CochainComplex.singleFunctor C 0).obj X ⟶ R.cochainComplex`
in `CochainComplex C ℤ` when `R` is an injective resolution of `X`. -/
/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quasi-isomorphism `(CochainComplex.singleFunctor C 0).obj X ⟶ R.cochainCompl
ex`
in `CochainComplex C ℤ` when `R` is an injective resolution of `X`.
-/
noncomputable def ι' : (CochainComplex.singleFunctor C 0).obj X ⟶ R.cochainComplex :=
  (HomologicalComplex.extendSingleIso _ _ _ _ (by simp)).inv ≫
    (ComplexShape.embeddingUpNat.extendFunctor C).map R.ι

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι'_f_zero :
    R.ι'.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom ≫ R.ι.f 0 ≫
      (R.cochainComplexXIso _ _ (by simp)).inv := by
  dsimp [ι']
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by simp),
    HomologicalComplex.extendSingleIso_inv_f]
  cat_disch

end

variable [Abelian C] {X : C} (R : InjectiveResolution X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : QuasiIso R.ι' := by dsimp [ι']; infer_instance
/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : R.cochainComplex.IsLE 0 := by
  simp only [← HomologicalComplex.isSupported_iff_of_quasiIso R.ι']
  infer_instance

namespace Hom

variable {R} {X' : C} {R' : InjectiveResolution X'} {f : X ⟶ X'}
  (φ : Hom R R' f)

/-- The morphism on cochain complexes indexed by `ℤ` that is induced by
an (heterogeneous) morphism of injective resolutions. -/
/-
**CategoryTheory.InjectiveResolution.Hom.hom'** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.InjectiveResolution.Hom`。
形式化陈述：hom' : R.cochainComplex ⟶ R'.cochainComplex
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
The morphism on cochain complexes indexed by `ℤ` that is induced by
an (heterogeneous) morphism of injective resolutions.
-/
noncomputable def hom' : R.cochainComplex ⟶ R'.cochainComplex :=
  HomologicalComplex.extendMap φ.hom _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.InjectiveResolution.Hom.hom'_f** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.InjectiveResolution.Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {X : C}   {R : CategoryTheory.InjectiveResolution X} {X' : C}
 {R' : CategoryTheory.InjectiveResolution X'} {f : X ⟶ X'}   (φ : R.Hom R' f) (n
 : ℤ) (m : ℕ) (h : ↑m = n),   φ.hom'.f n =     CategoryTheory.CategoryStruct.com
p (R.cochainComplexXIso n m h).hom       (CategoryTheory.CategoryStruct.comp (φ.
hom.f m) (R'.cochainComplexXIso n m h).inv)
参数：φ : R.Hom R' f；n : ℤ；m : ℕ；h : ↑m = n；R.cochainComplexXIso n m h；CategoryTheo
ry.CategoryStruct.comp (φ.hom.f m) (R'.cochainComplexXIso n m h).inv。
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
· 使用定理 `ComplexShape.embeddingUpNat_f`：∀ (n : ℕ), ComplexShape.embeddingUpNat.f 
n = ↑n
· 使用引理 `HomologicalComplex.extendMap_f`：extendMap_f {i : ι} {i' : ι'} (h : e.f i
 = i') : (extendMap φ e).f i' = (extendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e
 h).inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom'_f (n : ℤ) (m : ℕ) (h : m = n) :
    φ.hom'.f n =
    (R.cochainComplexXIso n m h).hom ≫ φ.hom.f m ≫ (R'.cochainComplexXIso n m h).inv := by
  simp [hom',
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := m) (i' := n) (by simpa),
    cochainComplexXIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.InjectiveResolution.Hom.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.InjectiveResolution.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι'_comp_hom' :
    R.ι' ≫ φ.hom' = (CochainComplex.singleFunctor C 0).map f ≫ R'.ι' :=
  HomologicalComplex.from_single_hom_ext (by
    simp [hom'_f _ 0 0 rfl, ι'_f_zero, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors,
      HomologicalComplex.single, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq])

end Hom

end InjectiveResolution

end CategoryTheory

