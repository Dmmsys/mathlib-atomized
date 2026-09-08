/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Localization.SmallShiftedHom

/-!
# Ext groups in abelian categories

Let `C` be an abelian category (with `C : Type u` and `Category.{v} C`).
In this file, we introduce the assumption `HasExt.{w} C` which asserts
that morphisms between single complexes in arbitrary degrees in
the derived category of `C` are `w`-small. Under this assumption,
we define `Ext.{w} X Y n : Type w` as shrunk versions of suitable
types of morphisms in the derived category. In particular, when `C` has
enough projectives or enough injectives, the property `HasExt.{v} C`
shall hold.

Note: in certain situations, `w := v` shall be the preferred
choice of universe (e.g. if `C := ModuleCat.{v} R` with `R : Type v`).
However, in the development of the API for Ext-groups, it is important
to keep a larger degree of generality for universes, as `w < v`
may happen in certain situations. Indeed, if `X : Scheme.{u}`,
then the underlying category of the étale site of `X` shall be a large
category. However, the category `Sheaf X.Etale AddCommGrpCat.{u}`
shall have good properties (because there is a small category of affine
schemes with the same category of sheaves), and even though the type of
morphisms in `Sheaf X.Etale AddCommGrpCat.{u}` shall be
in `Type (u + 1)`, these types are going to be `u`-small.
Then, for `C := Sheaf X.etale AddCommGrpCat.{u}`, we will have
`Category.{u + 1} C`, but `HasExt.{u} C` will hold
(as `C` has enough injectives). Then, the `Ext` groups between étale
sheaves over `X` shall be in `Type u`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w'' w' w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

open Localization Limits ZeroObject DerivedCategory Pretriangulated

/-- The property that morphisms between single complexes in arbitrary degrees are `w`-small
in the derived category. -/
/-
**CategoryTheory.HasExt** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：HasExt : Prop
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
The property that morphisms between single complexes in arbitrary degrees are `w
`-small
in the derived category.
-/
abbrev HasExt : Prop :=
  ∀ (X Y : C), HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ
    ((CochainComplex.singleFunctor C 0).obj X) ((CochainComplex.singleFunctor C 0).obj Y)
/-
**CategoryTheory.hasExt_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：hasExt_iff [HasDerivedCategory.{w'} C] : HasExt.{w} C ↔ forall (X Y : C) (
n : Int) (_ : 0 <= n), Small.{w} ((singleFunctor C 0).obj X ⟶ (((singleFunctor C
 0).obj Y)⟦n⟧))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `CategoryTheory.Localization.hasSmallLocalizedShiftedHom_iff`：hasSmallLoc
alizedShiftedHom_iff (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M] (X Y : C) 
: HasSmallLocalizedShiftedHom.{w} W M X Y ↔ foral…
· 使用定理 `DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `small_congr`：small_congr {α : Type*} {β : Type*} (e : α ≃ β) : Small.{w}
 α ↔ Small.{w} β
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instIsEquivalenceShiftFunctor`：∀ (C : Type u) {A : Type u
_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddGroup A]   [inst_2 : 
CategoryTheory.HasShift C A] (i : …
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `Int.sub_add_cancel`：∀ (a b : ℤ), a - b + b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.Functor.instIsSplitMonoApp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用引理 `CochainComplex.isStrictlyLE_shift`：isStrictlyLE_shift (n : Int) [K.IsStr
ictlyLE n] (a n' : Int) (h : a + n' = n) : (K⟦a⟧).IsStrictlyLE n'
· 使用定理 `CochainComplex.instIsStrictlyLEObjIntSingleFunctor`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用引理 `CochainComplex.isStrictlyGE_shift`：isStrictlyGE_shift (n : Int) [K.IsStr
ictlyGE n] (a n' : Int) (h : a + n' = n) : (K⟦a⟧).IsStrictlyGE n'
（共 36 条，此处仅展示前 30 条）
-/
lemma hasExt_iff [HasDerivedCategory.{w'} C] :
    HasExt.{w} C ↔ ∀ (X Y : C) (n : ℤ) (_ : 0 ≤ n), Small.{w}
      ((singleFunctor C 0).obj X ⟶
        (((singleFunctor C 0).obj Y)⟦n⟧)) := by
  dsimp [HasExt]
  simp only [hasSmallLocalizedShiftedHom_iff _ _ Q]
  constructor
  · intro h X Y n hn
    exact (small_congr ((shiftFunctorZero _ ℤ).app
      ((singleFunctor C 0).obj X)).homFromEquiv).1 (h X Y 0 n)
  · intro h X Y a b
    obtain hab | hab := le_or_gt a b
    · refine (small_congr ?_).1 (h X Y (b - a) (by simpa))
      exact (Functor.FullyFaithful.ofFullyFaithful
        (shiftFunctor _ a)).homEquiv.trans
        ((shiftFunctorAdd' _ _ _ _ (Int.sub_add_cancel b a)).symm.app _).homToEquiv
    · suffices Subsingleton ((Q.obj ((CochainComplex.singleFunctor C 0).obj X))⟦a⟧ ⟶
          (Q.obj ((CochainComplex.singleFunctor C 0).obj Y))⟦b⟧) from inferInstance
      constructor
      intro x y
      rw [← cancel_mono ((Q.commShiftIso b).inv.app _),
        ← cancel_epi ((Q.commShiftIso a).hom.app _)]
      have : (((CochainComplex.singleFunctor C 0).obj X)⟦a⟧).IsStrictlyLE (-a) :=
        CochainComplex.isStrictlyLE_shift _ 0 _ _ (by lia)
      have : (((CochainComplex.singleFunctor C 0).obj Y)⟦b⟧).IsStrictlyGE (-b) :=
        CochainComplex.isStrictlyGE_shift _ 0 _ _ (by lia)
      apply (subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE _ _ (-a) (-b) (by
        lia)).elim
/-
**CategoryTheory.hasExt_of_hasDerivedCategory** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：hasExt_of_hasDerivedCategory [HasDerivedCategory.{w} C] : HasExt.{w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.hasExt_iff`：hasExt_iff [HasDerivedCategory.{w'} C] : HasE
xt.{w} C ↔ forall (X Y : C) (n : Int) (_ : 0 <= n), Small.{w} ((singleFunctor C 
0).obj X ⟶ (((s…
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
-/
lemma hasExt_of_hasDerivedCategory [HasDerivedCategory.{w} C] : HasExt.{w} C := by
  rw [hasExt_iff.{w}]
  infer_instance
/-
**CategoryTheory.HasExt.standard** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.HasEx
t`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C], CategoryTheory.HasExt C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.hasExt_of_hasDerivedCategory`：hasExt_of_hasDerivedCategor
y [HasDerivedCategory.{w} C] : HasExt.{w} C
-/
lemma HasExt.standard : HasExt.{max u v} C := by
  let := HasDerivedCategory.standard
  exact hasExt_of_hasDerivedCategory _
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasExt.{w} C] (X Y : C) (a b : ℤ) [HasDerivedCategory.{w'} C] :
    Small.{w} ((singleFunctor C a).obj X ⟶ (singleFunctor C b).obj Y) := by
  have (a b : ℤ) :
      Small.{w} (((singleFunctor C 0).obj X)⟦a⟧ ⟶ ((singleFunctor C 0).obj Y)⟦b⟧) :=
    (hasSmallLocalizedShiftedHom_iff.{w}
      (W := (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))) (M := ℤ)
      (X := (CochainComplex.singleFunctor C 0).obj X)
      (Y := (CochainComplex.singleFunctor C 0).obj Y) Q).1 inferInstance a b
  exact small_of_injective
    (β := ((singleFunctor C 0).obj X)⟦-a⟧ ⟶ ((singleFunctor C 0).obj Y)⟦-b⟧)
    (f := fun φ ↦
      ((singleFunctors C).shiftIso (-a) a 0 (by simp)).hom.app X ≫ φ ≫
        ((singleFunctors C).shiftIso (-b) b 0 (by simp)).inv.app Y)
    (fun φ₁ φ₂ h ↦ by simpa using h)

variable {C}

variable [HasExt.{w} C]

namespace Abelian

/-- An Ext-group in an abelian category `C`, defined as a `Type w` when `[HasExt.{w} C]`. -/
/-
**CategoryTheory.Abelian.Ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：Ext (X Y : C) (n : Nat) : Type w
参数：X Y : C；n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
An Ext-group in an abelian category `C`, defined as a `Type w` when `[HasExt.{w}
 C]`.
-/
def Ext (X Y : C) (n : ℕ) : Type w :=
  SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((CochainComplex.singleFunctor C 0).obj X)
    ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)

namespace Ext

variable {X Y Z T : C}

/-- The composition of `Ext`. -/
/-
**CategoryTheory.Abelian.Ext.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abel
ian.Ext`。
形式化陈述：comp {a b : Nat} (α : Ext X Y a) (β : Ext Y Z b) {c : Nat} (h : a + b = c)
 : Ext X Z c
参数：α : Ext X Y a；β : Ext Y Z b；h : a + b = c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
The composition of `Ext`.
-/
noncomputable def comp {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    Ext X Z c :=
  SmallShiftedHom.comp α β (by lia)
/-
**CategoryTheory.Abelian.Ext.comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Abelian.Ext`。
形式化陈述：comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : Nat} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ
 : Ext Z T a₃) (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h : a₁ + a₂ + a₃ = a
) : (α.comp β h₁₂).comp γ (show a₁₂ + a₃ = a by lia) = α.comp (β.comp γ h₂₃) (by
 lia)
参数：α : Ext X Y a₁；β : Ext Y Z a₂；γ : Ext Z T a₃；h₁₂ : a₁ + a₂ = a₁₂；h₂₃ : a₂ + a
₃ = a₂₃；h : a₁ + a₂ + a₃ = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.SmallShiftedHom.comp_assoc`：comp_assoc {X Y 
Z T : C} {a₁ a₂ a₃ a₁₂ a₂₃ a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y] [Has
SmallLocalizedShiftedHom.{w} W M X Z] [HasSm…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
-/
lemma comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : ℕ} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T a₃)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h : a₁ + a₂ + a₃ = a) :
    (α.comp β h₁₂).comp γ (show a₁₂ + a₃ = a by lia) =
      α.comp (β.comp γ h₂₃) (by lia) :=
  SmallShiftedHom.comp_assoc _ _ _ _ _ _ (by lia)

@[simp]
/-
**CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Abelian.Ext`。
形式化陈述：comp_assoc_of_second_deg_zero {a₁ a₃ a₁₃ : Nat} (α : Ext X Y a₁) (β : Ext 
Y Z 0) (γ : Ext Z T a₃) (h₁₃ : a₁ + a₃ = a₁₃) : (α.comp β (add_zero _)).comp γ h
₁₃ = α.comp (β.comp γ (zero_add _)) h₁₃
参数：α : Ext X Y a₁；β : Ext Y Z 0；γ : Ext Z T a₃；h₁₃ : a₁ + a₃ = a₁₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.comp_assoc`：comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : 
Nat} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T a₃) (h₁₂ : a₁ + a₂ = a₁₂) (h
₂₃ : a₂ + a₃ = a₂₃) (h : a₁…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma comp_assoc_of_second_deg_zero
    {a₁ a₃ a₁₃ : ℕ} (α : Ext X Y a₁) (β : Ext Y Z 0) (γ : Ext Z T a₃)
    (h₁₃ : a₁ + a₃ = a₁₃) :
    (α.comp β (add_zero _)).comp γ h₁₃ = α.comp (β.comp γ (zero_add _)) h₁₃ := by
  apply comp_assoc
  lia

@[simp]
/-
**CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Abelian.Ext`。
形式化陈述：comp_assoc_of_third_deg_zero {a₁ a₂ a₁₂ : Nat} (α : Ext X Y a₁) (β : Ext Y
 Z a₂) (γ : Ext Z T 0) (h₁₂ : a₁ + a₂ = a₁₂) : (α.comp β h₁₂).comp γ (add_zero _
) = α.comp (β.comp γ (add_zero _)) h₁₂
参数：α : Ext X Y a₁；β : Ext Y Z a₂；γ : Ext Z T 0；h₁₂ : a₁ + a₂ = a₁₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.comp_assoc`：comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : 
Nat} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T a₃) (h₁₂ : a₁ + a₂ = a₁₂) (h
₂₃ : a₂ + a₃ = a₂₃) (h : a₁…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma comp_assoc_of_third_deg_zero
    {a₁ a₂ a₁₂ : ℕ} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T 0)
    (h₁₂ : a₁ + a₂ = a₁₂) :
    (α.comp β h₁₂).comp γ (add_zero _) = α.comp (β.comp γ (add_zero _)) h₁₂ := by
  apply comp_assoc
  lia

section

variable [HasDerivedCategory.{w'} C]

/-- When an instance of `[HasDerivedCategory.{w'} C]` is available, this is the bijection
between `Ext.{w} X Y n` and a type of morphisms in the derived category. -/
/-
**CategoryTheory.Abelian.Ext.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Abelian.Ext`。
形式化陈述：homEquiv {n : Nat} : Ext.{w} X Y n ≃ ShiftedHom ((singleFunctor C 0).obj X
) ((singleFunctor C 0).obj Y) (n : Int)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
When an instance of `[HasDerivedCategory.{w'} C]` is available, this is the bije
ction
between `Ext.{w} X Y n` and a type of morphisms in the derived category.
-/
noncomputable def homEquiv {n : ℕ} :
    Ext.{w} X Y n ≃ ShiftedHom ((singleFunctor C 0).obj X)
      ((singleFunctor C 0).obj Y) (n : ℤ) :=
  SmallShiftedHom.equiv (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) Q

/-- The morphism in the derived category which corresponds to an element in `Ext X Y a`. -/
/-
**CategoryTheory.Abelian.Ext.hom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Abe
lian.Ext`。
形式化陈述：hom {a : Nat} (α : Ext X Y a) : ShiftedHom ((singleFunctor C 0).obj X) ((s
ingleFunctor C 0).obj Y) (a : Int)
参数：α : Ext X Y a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism in the derived category which corresponds to an element in `Ext X Y
 a`.
-/
noncomputable abbrev hom {a : ℕ} (α : Ext X Y a) :
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (a : ℤ) :=
  homEquiv α

@[simp]
/-
**CategoryTheory.Abelian.Ext.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Abelian.Ext`。
形式化陈述：comp_hom {a b : Nat} (α : Ext X Y a) (β : Ext Y Z b) {c : Nat} (h : a + b 
= c) : (α.comp β h).hom = α.hom.comp β.hom (by lia)
参数：α : Ext X Y a；β : Ext Y Z b；h : a + b = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.SmallShiftedHom.equiv_comp`：equiv_comp [HasS
mallLocalizedShiftedHom.{w} W M X Y] [HasSmallLocalizedShiftedHom.{w} W M Y Z] [
HasSmallLocalizedShiftedHom.{w} W M X Z] [Ha…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
-/
lemma comp_hom {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    (α.comp β h).hom = α.hom.comp β.hom (by lia) := by
  apply SmallShiftedHom.equiv_comp

@[ext]
/-
**CategoryTheory.Abelian.Ext.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abeli
an.Ext`。
形式化陈述：ext {n : Nat} {α β : Ext X Y n} (h : α.hom = β.hom) : α = β
参数：h : α.hom = β.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma ext {n : ℕ} {α β : Ext X Y n} (h : α.hom = β.hom) : α = β :=
  homEquiv.injective h

end

/-- The canonical map `(X ⟶ Y) → Ext X Y 0`. -/
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `(X ⟶ Y) → Ext X Y 0`.
-/
noncomputable def mk₀ (f : X ⟶ Y) : Ext X Y 0 := SmallShiftedHom.mk₀ _ _ (by simp)
  ((CochainComplex.singleFunctor C 0).map f)

@[simp]
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_hom [HasDerivedCategory.{w'} C] (f : X ⟶ Y) :
    (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map f) := by
  apply SmallShiftedHom.equiv_mk₀

@[simp]
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk₀ f).comp (mk₀ g) (zero_add 0) = mk₀ (f ≫ g) := by
  let := HasDerivedCategory.standard C; ext; simp

@[simp]
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_comp_mk₀_assoc (f : X ⟶ Y) (g : Y ⟶ Z) {n : ℕ} (α : Ext Z T n) :
    (mk₀ f).comp ((mk₀ g).comp α (zero_add n)) (zero_add n) =
      (mk₀ (f ≫ g)).comp α (zero_add n) := by
  rw [← mk₀_comp_mk₀, comp_assoc]
  lia


variable (X Y) in
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_bijective : Function.Bijective (mk₀ (X := X) (Y := Y)) := by
  let := HasDerivedCategory.standard C
  have h : (singleFunctor C 0).FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  let e : (X ⟶ Y) ≃ Ext X Y 0 :=
    (h.homEquiv.trans (ShiftedHom.homEquiv _ (by simp))).trans homEquiv.symm
  have he : e.toFun = mk₀ := by
    ext f : 1
    dsimp [e]
    apply homEquiv.injective
    apply (Equiv.apply_symm_apply _ _).trans
    symm
    apply SmallShiftedHom.equiv_mk₀
  rw [← he]
  exact e.bijective

/-- The bijection `Ext X Y 0 ≃ (X ⟶ Y)`. -/
@[simps! symm_apply]
/-
**CategoryTheory.Abelian.Ext.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Abelian.Ext`。
形式化陈述：homEquiv {n : Nat} : Ext.{w} X Y n ≃ ShiftedHom ((singleFunctor C 0).obj X
) ((singleFunctor C 0).obj Y) (n : Int)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
The bijection `Ext X Y 0 ≃ (X ⟶ Y)`.
-/
noncomputable def homEquiv₀ : Ext X Y 0 ≃ (X ⟶ Y) :=
  (Equiv.ofBijective _ (mk₀_bijective X Y)).symm

@[simp]
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_homEquiv₀_apply (f : Ext X Y 0) :
    mk₀ (homEquiv₀ f) = f :=
  homEquiv₀.left_inv f

variable {n : ℕ}

/-! The abelian group structure on `Ext X Y n` is defined by transporting the
abelian group structure on the constructed derived category
(given by `HasDerivedCategory.standard`). This constructed derived category
is used in order to obtain most of the compatibilities satisfied by
this abelian group structure. It is then shown that the bijection
`homEquiv` between `Ext X Y n` and Hom-types in the derived category
can be promoted to an additive equivalence for any `[HasDerivedCategory C]` instance. -/

/-
**CategoryTheory.Abelian.Ext.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian.
Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The abelian group structure on `Ext X Y n` is defined by transporting the
abelian group structure on the constructed derived category
(given by `HasDerivedCategory.standard`). This constructed derived category
is used in order to obtain most of the compatibilities satisfied by
this abelian group structure. It is then shown that the bijection
`homEquiv` between `Ext X Y n` and Hom-types in the derived category
can be promoted to an additive equivalence for any `[HasDerivedCategory C]` inst
ance.
-/
noncomputable instance : AddCommGroup (Ext X Y n) :=
  letI := HasDerivedCategory.standard C
  homEquiv.addCommGroup

/-- The map from `Ext X Y n` to a `ShiftedHom` type in the *constructed* derived
category given by `HasDerivedCategory.standard`: this definition is introduced
only in order to prove properties of the abelian group structure on `Ext`-groups.
Do not use this definition: use the more general `hom` instead. -/
/-
**CategoryTheory.Abelian.Ext.hom'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Ab
elian.Ext`。
形式化陈述：hom' (α : Ext X Y n) : letI
参数：α : Ext X Y n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from `Ext X Y n` to a `ShiftedHom` type in the *constructed* derived
category given by `HasDerivedCategory.standard`: this definition is introduced
only in order to prove properties of the abelian group structure on `Ext`-groups
.
Do not use this definition: use the more general `hom` instead.
-/
noncomputable abbrev hom' (α : Ext X Y n) :
    letI := HasDerivedCategory.standard C
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ) :=
  letI := HasDerivedCategory.standard C
  α.hom
/-
**CategoryTheory.Abelian.Ext.add_hom'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma add_hom' (α β : Ext X Y n) : (α + β).hom' = α.hom' + β.hom' :=
  letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)
/-
**CategoryTheory.Abelian.Ext.neg_hom'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma neg_hom' (α : Ext X Y n) : (-α).hom' = -α.hom' :=
  letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)

variable (X Y n) in
/-
**CategoryTheory.Abelian.Ext.zero_hom'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma zero_hom' : (0 : Ext X Y n).hom' = 0 :=
  letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)

@[simp]
/-
**CategoryTheory.Abelian.Ext.add_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Abelian.Ext`。
形式化陈述：add_comp (α₁ α₂ : Ext X Y n) {m : Nat} (β : Ext Y Z m) {p : Nat} (h : n + 
m = p) : (α₁ + α₂).comp β h = α₁.comp β h + α₂.comp β h
参数：α₁ α₂ : Ext X Y n；β : Ext Y Z m；h : n + m = p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用定理 `_private.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic.0.CategoryTh
eory.Abelian.Ext.add_hom'`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u}
 C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : CategoryTheory.HasExt C] {X 
Y : C} …
· 使用引理 `CategoryTheory.ShiftedHom.add_comp`：add_comp {a b c : M} (α₁ α₂ : Shifte
dHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) : (α₁ + α₂).comp β h = α₁.com
p β h + α₂.comp β h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_comp (α₁ α₂ : Ext X Y n) {m : ℕ} (β : Ext Y Z m) {p : ℕ} (h : n + m = p) :
    (α₁ + α₂).comp β h = α₁.comp β h + α₂.comp β h := by
  let := HasDerivedCategory.standard C; ext; simp [this, add_hom']

@[simp]
/-
**CategoryTheory.Abelian.Ext.comp_add** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Abelian.Ext`。
形式化陈述：comp_add (α : Ext X Y n) {m : Nat} (β₁ β₂ : Ext Y Z m) {p : Nat} (h : n + 
m = p) : α.comp (β₁ + β₂) h = α.comp β₁ h + α.comp β₂ h
参数：α : Ext X Y n；β₁ β₂ : Ext Y Z m；h : n + m = p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用定理 `_private.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic.0.CategoryTh
eory.Abelian.Ext.add_hom'`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u}
 C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : CategoryTheory.HasExt C] {X 
Y : C} …
· 使用引理 `CategoryTheory.ShiftedHom.comp_add`：comp_add [forall (a : M), (shiftFunc
tor C a).Additive] {a b c : M} (α : ShiftedHom X Y a) (β₁ β₂ : ShiftedHom Y Z b)
 (h : b + a = c) : α.com…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_add (α : Ext X Y n) {m : ℕ} (β₁ β₂ : Ext Y Z m) {p : ℕ} (h : n + m = p) :
    α.comp (β₁ + β₂) h = α.comp β₁ h + α.comp β₂ h := by
  let := HasDerivedCategory.standard C; ext; simp [this, add_hom']

@[simp]
/-
**CategoryTheory.Abelian.Ext.neg_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Abelian.Ext`。
形式化陈述：neg_comp (α : Ext X Y n) {m : Nat} (β : Ext Y Z m) {p : Nat} (h : n + m = 
p) : (-α).comp β h = -α.comp β h
参数：α : Ext X Y n；β : Ext Y Z m；h : n + m = p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用定理 `_private.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic.0.CategoryTh
eory.Abelian.Ext.neg_hom'`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u}
 C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : CategoryTheory.HasExt C] {X 
Y : C} …
· 使用引理 `CategoryTheory.ShiftedHom.neg_comp`：neg_comp {a b c : M} (α : ShiftedHom
 X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) : (-α).comp β h = -α.comp β h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma neg_comp (α : Ext X Y n) {m : ℕ} (β : Ext Y Z m) {p : ℕ} (h : n + m = p) :
    (-α).comp β h = -α.comp β h := by
  let := HasDerivedCategory.standard C; ext; simp [this, neg_hom']

@[simp]
/-
**CategoryTheory.Abelian.Ext.comp_neg** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Abelian.Ext`。
形式化陈述：comp_neg (α : Ext X Y n) {m : Nat} (β : Ext Y Z m) {p : Nat} (h : n + m = 
p) : α.comp (-β) h = -α.comp β h
参数：α : Ext X Y n；β : Ext Y Z m；h : n + m = p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用定理 `_private.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic.0.CategoryTh
eory.Abelian.Ext.neg_hom'`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u}
 C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : CategoryTheory.HasExt C] {X 
Y : C} …
· 使用引理 `CategoryTheory.ShiftedHom.comp_neg`：comp_neg [forall (a : M), (shiftFunc
tor C a).Additive] {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h 
: b + a = c) : α.comp (-…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_neg (α : Ext X Y n) {m : ℕ} (β : Ext Y Z m) {p : ℕ} (h : n + m = p) :
    α.comp (-β) h = -α.comp β h := by
  let := HasDerivedCategory.standard C; ext; simp [this, neg_hom']

variable (X n) in
@[simp]
/-
**CategoryTheory.Abelian.Ext.zero_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Abelian.Ext`。
形式化陈述：zero_comp {m : Nat} (β : Ext Y Z m) (p : Nat) (h : n + m = p) : (0 : Ext X
 Y n).comp β h = 0
参数：β : Ext Y Z m；p : Nat；h : n + m = p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用定理 `_private.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic.0.CategoryTh
eory.Abelian.Ext.zero_hom'`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u
} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : CategoryTheory.HasExt C] (X
 Y : C) …
· 使用引理 `CategoryTheory.ShiftedHom.zero_comp`：zero_comp (a : M) {b c : M} (β : Sh
iftedHom Y Z b) (h : b + a = c) : (0 : ShiftedHom X Y a).comp β h = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero_comp {m : ℕ} (β : Ext Y Z m) (p : ℕ) (h : n + m = p) :
    (0 : Ext X Y n).comp β h = 0 := by
  let := HasDerivedCategory.standard C; ext; simp [this, zero_hom']

@[simp]
/-
**CategoryTheory.Abelian.Ext.comp_zero** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Abelian.Ext`。
形式化陈述：comp_zero (α : Ext X Y n) (Z : C) (m : Nat) (p : Nat) (h : n + m = p) : α.
comp (0 : Ext Y Z m) h = 0
参数：α : Ext X Y n；Z : C；m : Nat；p : Nat；h : n + m = p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用定理 `_private.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic.0.CategoryTh
eory.Abelian.Ext.zero_hom'`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u
} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : CategoryTheory.HasExt C] (X
 Y : C) …
· 使用引理 `CategoryTheory.ShiftedHom.comp_zero`：comp_zero [forall (a : M), (shiftFu
nctor C a).PreservesZeroMorphisms] {a : M} (β : ShiftedHom X Y a) {b c : M} (h :
 b + a = c) : β.comp (0 :…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_zero (α : Ext X Y n) (Z : C) (m : ℕ) (p : ℕ) (h : n + m = p) :
    α.comp (0 : Ext Y Z m) h = 0 := by
  let := HasDerivedCategory.standard C; ext; simp [this, zero_hom']

@[simp]
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_id_comp (α : Ext X Y n) :
    (mk₀ (𝟙 X)).comp α (zero_add n) = α := by
  let := HasDerivedCategory.standard C; ext; simp

@[simp]
/-
**CategoryTheory.Abelian.Ext.comp_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.A
belian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_mk₀_id (α : Ext X Y n) :
    α.comp (mk₀ (𝟙 Y)) (add_zero n) = α := by
  let := HasDerivedCategory.standard C; ext; simp

variable (X Y) in
@[simp]
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_zero : mk₀ (0 : X ⟶ Y) = 0 := by
  let := HasDerivedCategory.standard C; ext; simp [zero_hom']
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_add (f g : X ⟶ Y) : mk₀ (f + g) = mk₀ f + mk₀ g := by
  let := HasDerivedCategory.standard C; ext; simp [add_hom', ShiftedHom.mk₀]

/-- The additive bijection `Ext X Y 0 ≃+ (X ⟶ Y)`. -/
@[simps! symm_apply]
/-
**CategoryTheory.Abelian.Ext.addEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive bijection `Ext X Y 0 ≃+ (X ⟶ Y)`.
-/
noncomputable def addEquiv₀ : Ext X Y 0 ≃+ (X ⟶ Y) where
  toEquiv := homEquiv₀
  map_add' x y := homEquiv₀.symm.injective (by simp [mk₀_add])

@[simp]
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_addEquiv₀_apply (f : Ext X Y 0) :
    mk₀ (addEquiv₀ f) = f :=
  addEquiv₀.left_inv f

@[simp]
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_eq_zero_iff {M N : C} (f : M ⟶ N) :
    Ext.mk₀ f = 0 ↔ f = 0 :=
  Ext.addEquiv₀.symm.map_eq_zero_iff (x := f)

@[simp]
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_neg (f : X ⟶ Y) :
    mk₀ (-f) = -mk₀ f := by
  let := HasDerivedCategory.standard C; ext; simp [neg_hom']

section

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts in
/-
**CategoryTheory.Abelian.Ext.biprod_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Abelian.Ext`。
形式化陈述：biprod_ext {X₁ X₂ : C} {α β : Ext (X₁ ⊞ X₂) Y n} (h₁ : (mk₀ biprod.inl).co
mp α (zero_add n) = (mk₀ biprod.inl).comp β (zero_add n)) (h₂ : (mk₀ biprod.inr)
.comp α (zero_add n) = (mk₀ biprod.inr).comp β (zero_add n)) : α = β
参数：X₁ ⊞ X₂；h₁ : (mk₀ biprod.inl).comp α (zero_add n) = (mk₀ biprod.inl).comp β (
zero_add n)；h₂ : (mk₀ biprod.inr).comp α (zero_add n) = (mk₀ biprod.inr).comp β 
(zero_add n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.Ext.ext_iff`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : CategoryThe
ory.HasExt C] {X Y : C} …
· 使用定理 `CategoryTheory.Limits.BinaryCofan.IsColimit.hom_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Bin
aryCofan X Y}   (h : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `DerivedCategory.instAdditiveSingleFunctor`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasD
erivedCategory C] (n : ℤ), (Der…
· 使用定理 `CategoryTheory.Limits.PreservesBinaryBiproducts.preserves`：∀ {C : Type u
₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryT
heory.Category.{v₂, u₂} D}   {inst_2 : Category…
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts`：
preservesBinaryBiproducts_of_preservesBiproducts (F : C ⥤ D) [PreservesZeroMorph
isms F] [PreservesBiproductsOfShape WalkingPair F] : Preserv…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteBiproducts.preserves`：∀ {C : Type u
₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryT
heory.Category.{v₂, u₂} D}   {inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive`：∀ {C : Type 
u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Category
Theory.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_hom`：mk₀_hom [HasDerivedCategory.{w'} C] 
(f : X ⟶ Y) : (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map 
f)
· 使用引理 `CategoryTheory.ShiftedHom.mk₀_comp`：mk₀_comp (m₀ : M) (hm₀ : m₀ = 0) (f 
: X ⟶ Y) {a : M} (g : ShiftedHom Y Z a) : (mk₀ m₀ hm₀ f).comp g (by rw [hm₀, add
_zero]) = f ≫ g
-/
lemma biprod_ext {X₁ X₂ : C} {α β : Ext (X₁ ⊞ X₂) Y n}
    (h₁ : (mk₀ biprod.inl).comp α (zero_add n) = (mk₀ biprod.inl).comp β (zero_add n))
    (h₂ : (mk₀ biprod.inr).comp α (zero_add n) = (mk₀ biprod.inr).comp β (zero_add n)) :
    α = β := by
  let := HasDerivedCategory.standard C
  rw [Ext.ext_iff] at h₁ h₂ ⊢
  simp only [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp] at h₁ h₂
  apply BinaryCofan.IsColimit.hom_ext
    (isBinaryBilimitOfPreserves (singleFunctor C 0)
      (BinaryBiproduct.isBilimit X₁ X₂)).isColimit
  all_goals assumption

variable [HasDerivedCategory.{w'} C]

variable (X Y n) in
@[simp]
/-
**CategoryTheory.Abelian.Ext.zero_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Abelian.Ext`。
形式化陈述：zero_hom : (0 : Ext X Y n).hom = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用引理 `CategoryTheory.Functor.map_isZero`：map_isZero (F : C ⥤ D) [PreservesZero
Morphisms F] {X : C} (hX : IsZero X) : IsZero (F.obj X)
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `DerivedCategory.instAdditiveSingleFunctor`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasD
erivedCategory C] (n : ℤ), (Der…
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.comp_zero`：comp_zero (α : Ext X Y n) (Z : C) 
(m : Nat) (p : Nat) (h : n + m = p) : α.comp (0 : Ext Y Z m) h = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用引理 `CategoryTheory.ShiftedHom.comp_zero`：comp_zero [forall (a : M), (shiftFu
nctor C a).PreservesZeroMorphisms] {a : M} (β : ShiftedHom X Y a) {b c : M} (h :
 b + a = c) : β.comp (0 :…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
-/
lemma zero_hom : (0 : Ext X Y n).hom = 0 := by
  let β : Ext 0 Y n := 0
  have hβ : β.hom = 0 := by apply (Functor.map_isZero _ (isZero_zero C)).eq_of_src
  have : (0 : Ext X Y n) = (0 : Ext X 0 0).comp β (zero_add n) := by simp [β]
  rw [this, comp_hom, hβ, ShiftedHom.comp_zero]

@[simp]
/-
**CategoryTheory.Abelian.Ext.add_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.A
belian.Ext`。
形式化陈述：add_hom (α β : Ext X Y n) : (α + β).hom = α.hom + β.hom
参数：α β : Ext X Y n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.comp_add`：comp_add (α : Ext X Y n) {m : Nat} 
(β₁ β₂ : Ext Y Z m) {p : Nat} (h : n + m = p) : α.comp (β₁ + β₂) h = α.comp β₁ h
 + α.comp β₂ h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc`：mk₀_comp_mk₀_assoc (f : X
 ⟶ Y) (g : Y ⟶ Z) {n : Nat} (α : Ext Z T n) : (mk₀ f).comp ((mk₀ g).comp α (zero
_add n)) (zero_add n) = (mk₀ (f ≫ g…
· 使用定理 `CategoryTheory.Abelian.Ext.comp.congr_simp`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Cat
egoryTheory.HasExt C] {X Y Z : C…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_id_comp`：mk₀_id_comp (α : Ext X Y n) : (m
k₀ (𝟙 X)).comp α (zero_add n) = α
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.Abelian.Ext.biprod_ext`：biprod_ext {X₁ X₂ : C} {α β : Ext
 (X₁ ⊞ X₂) Y n} (h₁ : (mk₀ biprod.inl).comp α (zero_add n) = (mk₀ biprod.inl).co
mp β (zero_add n)) (h₂ : (m…
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_zero`：mk₀_zero : mk₀ (0 : X ⟶ Y) = 0
· 使用引理 `CategoryTheory.Abelian.Ext.zero_comp`：zero_comp {m : Nat} (β : Ext Y Z m
) (p : Nat) (h : n + m = p) : (0 : Ext X Y n).comp β h = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_hom`：mk₀_hom [HasDerivedCategory.{w'} C] 
(f : X ⟶ Y) : (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map 
f)
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `CategoryTheory.ShiftedHom.comp_add`：comp_add [forall (a : M), (shiftFunc
tor C a).Additive] {a b c : M} (α : ShiftedHom X Y a) (β₁ β₂ : ShiftedHom Y Z b)
 (h : b + a = c) : α.com…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用引理 `CategoryTheory.ShiftedHom.mk₀_comp_mk₀_assoc`：mk₀_comp_mk₀_assoc (f : X 
⟶ Y) (g : Y ⟶ Z) {a : M} (ha : a = 0) {d : M} (h : ShiftedHom Z T d) : (mk₀ a ha
 f).comp ((mk₀ a ha g).comp h (sho…
· 使用定理 `CategoryTheory.ShiftedHom.mk₀.congr_simp`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2
 : CategoryTheory.HasShift C M…
（共 42 条，此处仅展示前 30 条）
-/
lemma add_hom (α β : Ext X Y n) : (α + β).hom = α.hom + β.hom := by
  let α' : Ext (X ⊞ X) Y n := (mk₀ biprod.fst).comp α (zero_add n)
  let β' : Ext (X ⊞ X) Y n := (mk₀ biprod.snd).comp β (zero_add n)
  have eq₁ : α + β = (mk₀ (biprod.lift (𝟙 X) (𝟙 X))).comp (α' + β') (zero_add n) := by
    simp [α', β']
  have eq₂ : α' + β' = homEquiv.symm (α'.hom + β'.hom) := by
    apply biprod_ext
    all_goals ext; simp [α', β', ← Functor.map_comp]
  simp only [eq₁, eq₂, comp_hom, Equiv.apply_symm_apply, ShiftedHom.comp_add]
  congr
  · dsimp [α']
    rw [comp_hom, mk₀_hom, mk₀_hom]
    dsimp
    rw [ShiftedHom.mk₀_comp_mk₀_assoc, ← Functor.map_comp,
      biprod.lift_fst, Functor.map_id, ShiftedHom.mk₀_id_comp]
  · dsimp [β']
    rw [comp_hom, mk₀_hom, mk₀_hom]
    dsimp
    rw [ShiftedHom.mk₀_comp_mk₀_assoc, ← Functor.map_comp,
      biprod.lift_snd, Functor.map_id, ShiftedHom.mk₀_id_comp]
/-
**CategoryTheory.Abelian.Ext.neg_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.A
belian.Ext`。
形式化陈述：neg_hom (α : Ext X Y n) : (-α).hom = -α.hom
参数：α : Ext X Y n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `CategoryTheory.Abelian.Ext.add_hom`：add_hom (α β : Ext X Y n) : (α + β).
hom = α.hom + β.hom
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用引理 `CategoryTheory.Abelian.Ext.zero_hom`：zero_hom : (0 : Ext X Y n).hom = 0
-/
lemma neg_hom (α : Ext X Y n) : (-α).hom = -α.hom := by
  rw [← add_right_inj α.hom, ← add_hom, add_neg_cancel, add_neg_cancel, zero_hom]

/-- When an instance of `[HasDerivedCategory.{w'} C]` is available, this is the additive
bijection between `Ext.{w} X Y n` and a type of morphisms in the derived category. -/
/-
**CategoryTheory.Abelian.Ext.homAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Abelian.Ext`。
形式化陈述：homAddEquiv {n : Nat} : Ext.{w} X Y n ≃+ ShiftedHom ((singleFunctor C 0).o
bj X) ((singleFunctor C 0).obj Y) (n : Int) where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When an instance of `[HasDerivedCategory.{w'} C]` is available, this is the addi
tive
bijection between `Ext.{w} X Y n` and a type of morphisms in the derived categor
y.
-/
noncomputable def homAddEquiv {n : ℕ} :
    Ext.{w} X Y n ≃+
      ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ) where
  toEquiv := homEquiv
  map_add' := by simp

@[simp]
/-
**CategoryTheory.Abelian.Ext.homAddEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Abelian.Ext`。
形式化陈述：homAddEquiv_apply (α : Ext X Y n) : homAddEquiv α = α.hom
参数：α : Ext X Y n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homAddEquiv_apply (α : Ext X Y n) : homAddEquiv α = α.hom := rfl

end

variable (X Y Z) in
/-- The composition of `Ext`, as a bilinear map. -/
@[simps!]
/-
**CategoryTheory.Abelian.Ext.bilinearComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Abelian.Ext`。
形式化陈述：bilinearComp (a b c : Nat) (h : a + b = c) : Ext X Y a ->+ Ext Y Z b ->+ E
xt X Z c
参数：a b c : Nat；h : a + b = c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of `Ext`, as a bilinear map.
-/
noncomputable def bilinearComp (a b c : ℕ) (h : a + b = c) :
    Ext X Y a →+ Ext Y Z b →+ Ext X Z c :=
  AddMonoidHom.mk' (fun α ↦ AddMonoidHom.mk' (fun β ↦ α.comp β h) (by simp)) (by aesop)

/-- The postcomposition `Ext X Y a →+ Ext X Z b` with `β : Ext Y Z n` when `a + n = b`. -/
/-
**CategoryTheory.Abelian.Ext.postcomp** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Abelian.Ext`。
形式化陈述：postcomp (β : Ext Y Z n) (X : C) {a b : Nat} (h : a + n = b) : Ext X Y a -
>+ Ext X Z b
参数：β : Ext Y Z n；X : C；h : a + n = b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The postcomposition `Ext X Y a →+ Ext X Z b` with `β : Ext Y Z n` when `a + n = 
b`.
-/
noncomputable abbrev postcomp (β : Ext Y Z n) (X : C) {a b : ℕ} (h : a + n = b) :
    Ext X Y a →+ Ext X Z b :=
  (bilinearComp X Y Z a n b h).flip β

/-- The precomposition `Ext Y Z a →+ Ext X Z b` with `α : Ext X Y n` when `n + a = b`. -/
/-
**CategoryTheory.Abelian.Ext.precomp** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Abelian.Ext`。
形式化陈述：precomp (α : Ext X Y n) (Z : C) {a b : Nat} (h : n + a = b) : Ext Y Z a ->
+ Ext X Z b
参数：α : Ext X Y n；Z : C；h : n + a = b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The precomposition `Ext Y Z a →+ Ext X Z b` with `α : Ext X Y n` when `n + a = b
`.
-/
noncomputable abbrev precomp (α : Ext X Y n) (Z : C) {a b : ℕ} (h : n + a = b) :
    Ext Y Z a →+ Ext X Z b :=
  bilinearComp X Y Z n a b h α

end Ext

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `extFunctor`. -/
@[simps]
/-
**CategoryTheory.Abelian.extFunctorObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Abelian`。
形式化陈述：extFunctorObj (X : C) (n : Nat) : C ⥤ AddCommGrpCat.{w} where obj Y
参数：X : C；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `extFunctor`.
-/
noncomputable def extFunctorObj (X : C) (n : ℕ) : C ⥤ AddCommGrpCat.{w} where
  obj Y := AddCommGrpCat.of (Ext X Y n)
  map f := AddCommGrpCat.ofHom ((Ext.mk₀ f).postcomp _ (add_zero n))
  map_comp f f' := by
    ext α
    dsimp [AddCommGrpCat.ofHom]
    rw [← Ext.mk₀_comp_mk₀]
    symm
    apply Ext.comp_assoc
    lia

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor `Cᵒᵖ ⥤ C ⥤ AddCommGrpCat` which sends `X : C` and `Y : C`
to `Ext X Y n`. -/
@[simps]
/-
**CategoryTheory.Abelian.extFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ab
elian`。
形式化陈述：extFunctor (n : Nat) : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w} where obj X
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Cᵒᵖ ⥤ C ⥤ AddCommGrpCat` which sends `X : C` and `Y : C`
to `Ext X Y n`.
-/
noncomputable def extFunctor (n : ℕ) : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w} where
  obj X := extFunctorObj X.unop n
  map {X₁ X₂} f :=
    { app := fun Y ↦ AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun α ↦ (Ext.mk₀ f.unop).comp α (zero_add _)) (by simp))
      naturality := fun {Y₁ Y₂} g ↦ by
        ext α
        dsimp
        symm
        apply Ext.comp_assoc
        all_goals lia }
  map_comp {X₁ X₂ X₃} f f' := by
    ext Y α
    simp

section biproduct

attribute [local simp] Ext.mk₀_add

/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℕ) : (extFunctorObj X n).Additive where
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : (extFunctor (C := C) n).Additive where
/-
**CategoryTheory.Abelian.Ext.comp_sum** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Abelian.Ext`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.HasExt C] {X Y Z : C} {p : ℕ} (α :
 CategoryTheory.Abelian.Ext X Y p) {ι : Type u_1}   [inst_3 : Fintype ι] {q : ℕ}
 (β : ι → CategoryTheory.Abelian.Ext Y Z q) {n : ℕ} (h : p + q = n),   α.comp (∑
 i, β i) h = ∑ i, α.comp (β i) h
参数：α : CategoryTheory.Abelian.Ext X Y p；β : ι → CategoryTheory.Abelian.Ext Y Z q
；h : p + q = n；∑ i, β i；β i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma Ext.comp_sum {X Y Z : C} {p : ℕ} (α : Ext X Y p) {ι : Type*} [Fintype ι] {q : ℕ}
    (β : ι → Ext Y Z q) {n : ℕ} (h : p + q = n) :
    α.comp (∑ i, β i) h = ∑ i, α.comp (β i) h :=
  map_sum (α.precomp Z h) _ _
/-
**CategoryTheory.Abelian.Ext.sum_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Abelian.Ext`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.HasExt C] {X Y Z : C} {p : ℕ} {ι :
 Type u_1} [inst_3 : Fintype ι]   (α : ι → CategoryTheory.Abelian.Ext X Y p) {q 
: ℕ} (β : CategoryTheory.Abelian.Ext Y Z q) {n : ℕ} (h : p + q = n),   (∑ i, α i
).comp β h = ∑ i, (α i).comp β h
参数：α : ι → CategoryTheory.Abelian.Ext X Y p；β : CategoryTheory.Abelian.Ext Y Z q
；h : p + q = n；∑ i, α i；α i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma Ext.sum_comp {X Y Z : C} {p : ℕ} {ι : Type*} [Fintype ι] (α : ι → Ext X Y p) {q : ℕ}
    (β : Ext Y Z q) {n : ℕ} (h : p + q = n) :
    (∑ i, α i).comp β h = ∑ i, (α i).comp β h :=
  map_sum (β.postcomp X h) _ _
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ext.mk₀_sum {X Y : C} {ι : Type*} [Fintype ι] (f : ι → (X ⟶ Y)) :
    mk₀ (∑ i, f i) = ∑ i, mk₀ (f i) :=
  map_sum addEquiv₀.symm _ _

/-- `Ext` commutes with biproducts in its first variable. -/
/-
**CategoryTheory.Abelian.Ext.biproductAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Abelian.Ext`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       [inst_2 : CategoryTheory.HasExt C] →         
{J : Type u_1} →           [Fintype J] →             {X : J → C} →              
 {c : CategoryTheory.Limits.Bicone X} →                 c.IsBilimit →           
        (Y : C) →                     (n : ℕ) → CategoryTheory.Abelian.Ext c.pt 
Y n ≃+ ((i : J) → CategoryTheory.Abelian.Ext (X i) Y n)
参数：Y : C；n : ℕ；(i : J) → CategoryTheory.Abelian.Ext (X i) Y n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ext` commutes with biproducts in its first variable.
-/
noncomputable def Ext.biproductAddEquiv {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : ℕ) : Ext c.pt Y n ≃+ Π i, Ext (X i) Y n where
  toFun e i := (Ext.mk₀ (c.ι i)).comp e (zero_add n)
  invFun e := ∑ (i : J), (Ext.mk₀ (c.π i)).comp (e i) (zero_add n)
  left_inv x := by
    simp only [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀]
    rw [← Ext.sum_comp, ← Ext.mk₀_sum, IsBilimit.total hc, mk₀_id_comp]
  right_inv _ := by
    ext i
    simp only [Ext.comp_sum, ← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀]
    rw [Finset.sum_eq_single i _ (by simp), bicone_ι_π_self, mk₀_id_comp]
    intro _ _ hij
    rw [c.ι_π, dif_neg hij.symm, mk₀_zero, zero_comp]
  map_add' _ _ := by
    simp only [comp_add, Pi.add_def]

/-- `Ext` commutes with biproducts in its second variable. -/
/-
**CategoryTheory.Abelian.Ext.addEquivBiproduct** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Abelian.Ext`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       [inst_2 : CategoryTheory.HasExt C] →         
(X : C) →           {J : Type u_1} →             [Fintype J] →               {Y 
: J → C} →                 {c : CategoryTheory.Limits.Bicone Y} →               
    c.IsBilimit →                     (n : ℕ) → CategoryTheory.Abelian.Ext X c.p
t n ≃+ ((i : J) → CategoryTheory.Abelian.Ext X (Y i) n)
参数：X : C；n : ℕ；(i : J) → CategoryTheory.Abelian.Ext X (Y i) n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ext` commutes with biproducts in its second variable.
-/
noncomputable def Ext.addEquivBiproduct (X : C) {J : Type*} [Fintype J] {Y : J → C} {c : Bicone Y}
    (hc : c.IsBilimit) (n : ℕ) : Ext X c.pt n ≃+ Π i, Ext X (Y i) n where
  toFun e i := e.comp (Ext.mk₀ (c.π i)) (add_zero n)
  invFun e := ∑ (i : J), (e i).comp (Ext.mk₀ (c.ι i)) (add_zero n)
  left_inv _ := by
    simp only [comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, ← Ext.comp_sum,
      ← Ext.mk₀_sum, IsBilimit.total hc, comp_mk₀_id]
  right_inv _ := by
    ext i
    simp only [Ext.sum_comp, comp_assoc_of_second_deg_zero, mk₀_comp_mk₀]
    rw [Finset.sum_eq_single i _ (by simp), bicone_ι_π_self, comp_mk₀_id]
    intro _ _ hij
    rw [c.ι_π, dif_neg hij, mk₀_zero, comp_zero]
  map_add' _ _ := by
    simp only [add_comp, Pi.add_def]

end biproduct

/-- `Ext` commutes with binary biproducts on the first variable. -/
@[simps apply_fst apply_snd, simps -isSimp symm_apply]
/-
**CategoryTheory.Abelian.Ext.biprodAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Abelian.Ext`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       [inst_2 : CategoryTheory.HasExt C] →         
{X₁ X₂ Y : C} →           {n : ℕ} →             CategoryTheory.Abelian.Ext (X₁ ⊞
 X₂) Y n ≃+               CategoryTheory.Abelian.Ext X₁ Y n × CategoryTheory.Abe
lian.Ext X₂ Y n
参数：X₁ ⊞ X₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ext` commutes with binary biproducts on the first variable.
-/
noncomputable def Ext.biprodAddEquiv {X₁ X₂ Y : C} {n : ℕ} :
    Ext (X₁ ⊞ X₂) Y n ≃+ Ext X₁ Y n × Ext X₂ Y n where
  toFun e := ⟨(mk₀ biprod.inl).comp e (zero_add n), (mk₀ biprod.inr).comp e (zero_add n)⟩
  invFun e := (mk₀ biprod.fst).comp e.1 (zero_add n) + (mk₀ biprod.snd).comp e.2 (zero_add n)
  left_inv _ := by
    simp only [mk₀_comp_mk₀_assoc, ← add_comp, ← mk₀_add, biprod.total, mk₀_id_comp]
  right_inv _ := by simp
  map_add' := by simp

/-- `Ext` commutes with binary biproducts on the second variable. -/
@[simps apply_fst apply_snd, simps -isSimp symm_apply]
/-
**CategoryTheory.Abelian.Ext.addEquivBiprod** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Abelian.Ext`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       [inst_2 : CategoryTheory.HasExt C] →         
{X Y₁ Y₂ : C} →           {n : ℕ} →             CategoryTheory.Abelian.Ext X (Y₁
 ⊞ Y₂) n ≃+               CategoryTheory.Abelian.Ext X Y₁ n × CategoryTheory.Abe
lian.Ext X Y₂ n
参数：Y₁ ⊞ Y₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ext` commutes with binary biproducts on the second variable.
-/
noncomputable def Ext.addEquivBiprod {X : C} {Y₁ Y₂ : C} {n : ℕ} :
    Ext X (Y₁ ⊞ Y₂) n ≃+ Ext X Y₁ n × Ext X Y₂ n where
  toFun e := ⟨e.comp (mk₀ biprod.fst) (add_zero n), e.comp (mk₀ biprod.snd) (add_zero n)⟩
  invFun e := e.1.comp (mk₀ biprod.inl) (add_zero n) + e.2.comp (mk₀ biprod.inr) (add_zero n)
  left_inv e := by
    simp only [comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, ← comp_add, ← mk₀_add,
      biprod.total, comp_mk₀_id]
  right_inv _ := by simp
  map_add' := by simp

section ChangeOfUniverse

namespace Ext

variable [HasExt.{w'} C] {X Y : C} {n : ℕ}

/-- Up to an equivalence, the type `Ext.{w} X Y n` does not depend on the universe `w`. -/
/-
**CategoryTheory.Abelian.Ext.chgUniv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.A
belian.Ext`。
形式化陈述：chgUniv : Ext.{w} X Y n ≃ Ext.{w'} X Y n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
Up to an equivalence, the type `Ext.{w} X Y n` does not depend on the universe `
w`.
-/
noncomputable def chgUniv : Ext.{w} X Y n ≃ Ext.{w'} X Y n :=
  SmallShiftedHom.chgUniv.{w', w}
/-
**CategoryTheory.Abelian.Ext.homEquiv_chgUniv** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Abelian.Ext`。
形式化陈述：homEquiv_chgUniv [HasDerivedCategory.{w''} C] (e : Ext.{w} X Y n) : homEqu
iv.{w'', w'} (chgUniv.{w'} e) = homEquiv.{w'', w} e
参数：e : Ext.{w} X Y n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.SmallShiftedHom.equiv_chgUniv`：equiv_chgUniv
 (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M] {X Y : C} {m : M} [HasSmallLoc
alizedShiftedHom.{w} W M X Y] [HasSmallLocalize…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
-/
lemma homEquiv_chgUniv [HasDerivedCategory.{w''} C] (e : Ext.{w} X Y n) :
    homEquiv.{w'', w'} (chgUniv.{w'} e) = homEquiv.{w'', w} e := by
  apply SmallShiftedHom.equiv_chgUniv

end Ext

end ChangeOfUniverse

end Abelian

open Abelian

variable (C) in
/-
**CategoryTheory.hasExt_iff_small_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`
。
形式化陈述：hasExt_iff_small_ext : HasExt.{w'} C ↔ forall (X Y : C) (n : Nat), Small.{
w'} (Ext.{w} X Y n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `small_congr`：small_congr {α : Type*} {β : Type*} (e : α ≃ β) : Small.{w}
 α ↔ Small.{w} β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
-/
lemma hasExt_iff_small_ext :
    HasExt.{w'} C ↔ ∀ (X Y : C) (n : ℕ), Small.{w'} (Ext.{w} X Y n) := by
  let := HasDerivedCategory.standard C
  simp only [hasExt_iff, small_congr Ext.homEquiv]
  constructor
  · intro h X Y n
    exact h X Y n (by simp)
  · intro h X Y n hn
    lift n to ℕ using hn
    exact h X Y n

end CategoryTheory

