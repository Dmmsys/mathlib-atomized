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

/--
Definition of `HasExt` / `HasExt` 的定义

English:
abbreviation HasExt
  signature: : Prop
  body: forall (X Y : C), HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up Int)) Int
    ((CochainComplex.singleFunctor C 0).obj X) ((CochainComplex.singleFunctor C 0).obj Y)

中文:
缩写 HasExt
  签名: : 命题
  定义体: forall (X Y : C), HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up Int)) Int
    ((CochainComplex.singleFunctor C 0).obj X) ((CochainComplex.singleFunctor C 0).obj Y)

Depends on / 依赖: CochainComplex, CochainComplex.singleFunctor, ComplexShape, ComplexShape.up, HasSmallLocalizedShiftedHom, HomologicalComplex, HomologicalComplex.quasiIso, quasiIso, singleFunctor
-/
abbrev HasExt : Prop :=
  forall (X Y : C), HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up Int)) Int
    ((CochainComplex.singleFunctor C 0).obj X) ((CochainComplex.singleFunctor C 0).obj Y)

/--
lemma `hasExt_iff` / 引理 `hasExt_iff`

English:
lemma hasExt_iff
  given: [HasDerivedCategory.{w'} C]
  proof: by
  dsimp [HasExt]
  simp only [hasSmallLocalizedShiftedHom_iff _ _ Q]
  constructor
  · intro h X Y n hn
    exact (small_congr ((shiftFunctorZero _ Int).app
      ((singleFunctor C 0).obj X)).homFromEquiv).1 (h X Y 0 n)
  · intro h X Y a b
    obtain hab | hab := le_or_gt a b
    · refine (small_

中文:
引理 hasExt_iff
  条件: [HasDerivedCategory.{w'} C]
  证明: by
  dsimp [HasExt]
  simp only [hasSmallLocalizedShiftedHom_iff _ _ Q]
  constructor
  · intro h X Y n hn
    exact (small_congr ((shiftFunctorZero _ Int).app
      ((singleFunctor C 0).obj X)).homFromEquiv).1 (h X Y 0 n)
  · intro h X Y a b
    obtain hab | hab := le_or_gt a b
    · refine (small_

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.ofFullyFaithful, HasExt, Int.sub_add_cancel, Q.obj, Subsingleton, hasSmallLocalizedShiftedHom_iff, homEquiv, homEquiv.trans, homFromEquiv, homToEquiv, le_or_gt, ofFullyFaithful, shiftFunctor, shiftFunctorAdd, shiftFunctorZero, singleFunctor, small_congr, sub_add_cancel
-/
lemma hasExt_iff [HasDerivedCategory.{w'} C] :
    HasExt.{w} C ↔ forall (X Y : C) (n : Int) (_ : 0 <= n), Small.{w}
      ((singleFunctor C 0).obj X ⟶
        (((singleFunctor C 0).obj Y)⟦n⟧)) := by
  dsimp [HasExt]
  simp only [hasSmallLocalizedShiftedHom_iff _ _ Q]
  constructor
  · intro h X Y n hn
    exact (small_congr ((shiftFunctorZero _ Int).app
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
      rw [← cancel_mono ((Q.commShiftIso b).inv.app _)]; rw [← cancel_epi ((Q.commShiftIso a).hom.app _)]
      have : (((CochainComplex.singleFunctor C 0).obj X)⟦a⟧).IsStrictlyLE (-a) :=
        CochainComplex.isStrictlyLE_shift _ 0 _ _ (by lia)
      have : (((CochainComplex.singleFunctor C 0).obj Y)⟦b⟧).IsStrictlyGE (-b) :=
        CochainComplex.isStrictlyGE_shift _ 0 _ _ (by lia)
      apply (subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE _ _ (-a) (-b) (by
        lia)).elim

/--
lemma `hasExt_of_hasDerivedCategory` / 引理 `hasExt_of_hasDerivedCategory`

English:
lemma hasExt_of_hasDerivedCategory
  given: [HasDerivedCategory.{w} C]
  statement: HasExt.{w} C
  proof: by
  rw [hasExt_iff.{w}]
  infer_instance

中文:
引理 hasExt_of_hasDerivedCategory
  条件: [HasDerivedCategory.{w} C]
  结论: HasExt.{w} C
  证明: by
  rw [hasExt_iff.{w}]
  infer_instance

Depends on / 依赖: hasExt_iff, infer_instance
-/
lemma hasExt_of_hasDerivedCategory [HasDerivedCategory.{w} C] : HasExt.{w} C := by
  rw [hasExt_iff.{w}]
  infer_instance

/--
lemma `HasExt.standard` / 引理 `HasExt.standard`

English:
lemma HasExt.standard
  statement: HasExt.{max u v} C
  proof: by
  let := HasDerivedCategory.standard
  exact hasExt_of_hasDerivedCategory _

中文:
引理 HasExt.standard
  结论: HasExt.{最大值 u v} C
  证明: by
  let := HasDerivedCategory.standard
  exact hasExt_of_hasDerivedCategory _

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, hasExt_of_hasDerivedCategory, standard
-/
lemma HasExt.standard : HasExt.{max u v} C := by
  let := HasDerivedCategory.standard
  exact hasExt_of_hasDerivedCategory _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasExt.{w}
  signature: C] (X Y
  body: by
  have (a b : Int) :
      Small.{w} (((singleFunctor C 0).obj X)⟦a⟧ ⟶ ((singleFunctor C 0).obj Y)⟦b⟧) :=
    (hasSmallLocalizedShiftedHom_iff.{w}
      (W := (HomologicalComplex.quasiIso C (ComplexShape.up Int))) (M := Int)
      (X := (CochainComplex.singleFunctor C 0).obj X)
      (Y := (Cocha

中文:
实例 [HasExt.{w}
  签名: C] (X Y
  定义体: by
  have (a b : Int) :
      Small.{w} (((singleFunctor C 0).obj X)⟦a⟧ ⟶ ((singleFunctor C 0).obj Y)⟦b⟧) :=
    (hasSmallLocalizedShiftedHom_iff.{w}
      (W := (HomologicalComplex.quasiIso C (ComplexShape.up Int))) (M := Int)
      (X := (CochainComplex.singleFunctor C 0).obj X)
      (Y := (Cocha

Depends on / 依赖: CochainComplex, CochainComplex.singleFunctor, ComplexShape, ComplexShape.up, HomologicalComplex, HomologicalComplex.quasiIso, hasSmallLocalizedShiftedHom_iff, hom.app, quasiIso, shiftIso, singleFunctor, singleFunctors, small_of_injective
-/
instance [HasExt.{w} C] (X Y : C) (a b : Int) [HasDerivedCategory.{w'} C] :
    Small.{w} ((singleFunctor C a).obj X ⟶ (singleFunctor C b).obj Y) := by
  have (a b : Int) :
      Small.{w} (((singleFunctor C 0).obj X)⟦a⟧ ⟶ ((singleFunctor C 0).obj Y)⟦b⟧) :=
    (hasSmallLocalizedShiftedHom_iff.{w}
      (W := (HomologicalComplex.quasiIso C (ComplexShape.up Int))) (M := Int)
      (X := (CochainComplex.singleFunctor C 0).obj X)
      (Y := (CochainComplex.singleFunctor C 0).obj Y) Q).1 inferInstance a b
  exact small_of_injective
    (β := ((singleFunctor C 0).obj X)⟦-a⟧ ⟶ ((singleFunctor C 0).obj Y)⟦-b⟧)
    (f := fun φ =>
      ((singleFunctors C).shiftIso (-a) a 0 (by simp)).hom.app X ≫ φ ≫
        ((singleFunctors C).shiftIso (-b) b 0 (by simp)).inv.app Y)
    (fun φ₁ φ₂ h => by simpa using h)

variable {C}

variable [HasExt.{w} C]

namespace Abelian

/--
Definition of `Ext` / `Ext` 的定义

English:
definition Ext
  signature: (X Y : C) (n : Nat)
  body: SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up Int))
    ((CochainComplex.singleFunctor C 0).obj X)
    ((CochainComplex.singleFunctor C 0).obj Y) (n : Int)

中文:
定义 Ext
  签名: (X Y : C) (n : 自然数)
  定义体: SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up Int))
    ((CochainComplex.singleFunctor C 0).obj X)
    ((CochainComplex.singleFunctor C 0).obj Y) (n : Int)

Depends on / 依赖: CochainComplex, CochainComplex.singleFunctor, ComplexShape, ComplexShape.up, HomologicalComplex, HomologicalComplex.quasiIso, SmallShiftedHom, quasiIso, singleFunctor
-/
def Ext (X Y : C) (n : Nat) : Type w :=
  SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up Int))
    ((CochainComplex.singleFunctor C 0).obj X)
    ((CochainComplex.singleFunctor C 0).obj Y) (n : Int)

namespace Ext

variable {X Y Z T : C}

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {a b : Nat} (α : Ext X Y a) (β : Ext Y Z b) {c : Nat} (h : a + b = c)
  body: SmallShiftedHom.comp α β (by lia)

中文:
定义 comp
  签名: {a b : 自然数} (α : Ext X Y a) (β : Ext Y Z b) {c : 自然数} (h : a + b = c)
  定义体: SmallShiftedHom.comp α β (by lia)

Depends on / 依赖: SmallShiftedHom, SmallShiftedHom.comp
-/
noncomputable def comp {a b : Nat} (α : Ext X Y a) (β : Ext Y Z b) {c : Nat} (h : a + b = c) :
    Ext X Z c :=
  SmallShiftedHom.comp α β (by lia)

/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  statement: {a₁ a₂ a₃ a₁₂ a₂₃ a : Nat} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T a₃)
  proof: SmallShiftedHom.comp_assoc _ _ _ _ _ _ (by lia)

@[simp]

中文:
引理 comp_assoc
  结论: {a₁ a₂ a₃ a₁₂ a₂₃ a : 自然数} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T a₃)
  证明: SmallShiftedHom.comp_assoc _ _ _ _ _ _ (by lia)

@[simp]

Depends on / 依赖: SmallShiftedHom, SmallShiftedHom.comp_assoc, comp_assoc
-/
lemma comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : Nat} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T a₃)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h : a₁ + a₂ + a₃ = a) :
    (α.comp β h₁₂).comp γ (show a₁₂ + a₃ = a by lia) =
      α.comp (β.comp γ h₂₃) (by lia) :=
  SmallShiftedHom.comp_assoc _ _ _ _ _ _ (by lia)

@[simp]
/--
lemma `comp_assoc_of_second_deg_zero` / 引理 `comp_assoc_of_second_deg_zero`

English:
lemma comp_assoc_of_second_deg_zero
  proof: by
  apply comp_assoc
  lia

@[simp]

中文:
引理 comp_assoc_of_second_deg_zero
  证明: by
  apply comp_assoc
  lia

@[simp]

Depends on / 依赖: comp_assoc
-/
lemma comp_assoc_of_second_deg_zero
    {a₁ a₃ a₁₃ : Nat} (α : Ext X Y a₁) (β : Ext Y Z 0) (γ : Ext Z T a₃)
    (h₁₃ : a₁ + a₃ = a₁₃) :
    (α.comp β (add_zero _)).comp γ h₁₃ = α.comp (β.comp γ (zero_add _)) h₁₃ := by
  apply comp_assoc
  lia

@[simp]
/--
lemma `comp_assoc_of_third_deg_zero` / 引理 `comp_assoc_of_third_deg_zero`

English:
lemma comp_assoc_of_third_deg_zero
  proof: by
  apply comp_assoc
  lia

中文:
引理 comp_assoc_of_third_deg_zero
  证明: by
  apply comp_assoc
  lia

Depends on / 依赖: comp_assoc
-/
lemma comp_assoc_of_third_deg_zero
    {a₁ a₂ a₁₂ : Nat} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T 0)
    (h₁₂ : a₁ + a₂ = a₁₂) :
    (α.comp β h₁₂).comp γ (add_zero _) = α.comp (β.comp γ (add_zero _)) h₁₂ := by
  apply comp_assoc
  lia

section

variable [HasDerivedCategory.{w'} C]

/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: {n : Nat}
  body: SmallShiftedHom.equiv (HomologicalComplex.quasiIso C (ComplexShape.up Int)) Q

中文:
定义 homEquiv
  签名: {n : 自然数}
  定义体: SmallShiftedHom.equiv (HomologicalComplex.quasiIso C (ComplexShape.up Int)) Q

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplex, HomologicalComplex.quasiIso, SmallShiftedHom, SmallShiftedHom.equiv, quasiIso
-/
noncomputable def homEquiv {n : Nat} :
    Ext.{w} X Y n ≃ ShiftedHom ((singleFunctor C 0).obj X)
      ((singleFunctor C 0).obj Y) (n : Int) :=
  SmallShiftedHom.equiv (HomologicalComplex.quasiIso C (ComplexShape.up Int)) Q

/--
Definition of `hom` / `hom` 的定义

English:
abbreviation hom
  signature: {a : Nat} (α : Ext X Y a)
  body: homEquiv α

@[simp]

中文:
缩写 hom
  签名: {a : 自然数} (α : Ext X Y a)
  定义体: homEquiv α

@[simp]

Depends on / 依赖: homEquiv
-/
noncomputable abbrev hom {a : Nat} (α : Ext X Y a) :
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (a : Int) :=
  homEquiv α

@[simp]
/--
lemma `comp_hom` / 引理 `comp_hom`

English:
lemma comp_hom
  given: {a b : Nat} (α : Ext X Y a) (β : Ext Y Z b) {c : Nat} (h : a + b = c)
  proof: by
  apply SmallShiftedHom.equiv_comp

@[ext]

中文:
引理 comp_hom
  条件: {a b : 自然数} (α : Ext X Y a) (β : Ext Y Z b) {c : 自然数} (h : a + b = c)
  证明: by
  apply SmallShiftedHom.equiv_comp

@[ext]

Depends on / 依赖: SmallShiftedHom, SmallShiftedHom.equiv_comp, equiv_comp
-/
lemma comp_hom {a b : Nat} (α : Ext X Y a) (β : Ext Y Z b) {c : Nat} (h : a + b = c) :
    (α.comp β h).hom = α.hom.comp β.hom (by lia) := by
  apply SmallShiftedHom.equiv_comp

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {n : Nat} {α β : Ext X Y n} (h : α.hom = β.hom)
  statement: α = β
  proof: homEquiv.injective h

中文:
引理 ext
  条件: {n : 自然数} {α β : Ext X Y n} (h : α.hom = β.hom)
  结论: α = β
  证明: homEquiv.injective h

Depends on / 依赖: homEquiv, homEquiv.injective, injective
-/
lemma ext {n : Nat} {α β : Ext X Y n} (h : α.hom = β.hom) : α = β :=
  homEquiv.injective h

end

/--
Definition of `mk₀` / `mk₀` 的定义

English:
definition mk₀
  signature: (f : X ⟶ Y)
  body: SmallShiftedHom.mk₀ _ _ (by simp)
  ((CochainComplex.singleFunctor C 0).map f)

@[simp]

中文:
定义 mk₀
  签名: (f : X ⟶ Y)
  定义体: SmallShiftedHom.mk₀ _ _ (by simp)
  ((CochainComplex.singleFunctor C 0).map f)

@[simp]

Depends on / 依赖: SmallShiftedHom, SmallShiftedHom.mk
-/
noncomputable def mk₀ (f : X ⟶ Y) : Ext X Y 0 := SmallShiftedHom.mk₀ _ _ (by simp)
  ((CochainComplex.singleFunctor C 0).map f)

@[simp]
/--
lemma `mk₀_hom` / 引理 `mk₀_hom`

English:
lemma mk₀_hom
  given: [HasDerivedCategory.{w'} C] (f : X ⟶ Y)
  proof: by
  apply SmallShiftedHom.equiv_mk₀

@[simp]

中文:
引理 mk₀_hom
  条件: [HasDerivedCategory.{w'} C] (f : X ⟶ Y)
  证明: by
  apply SmallShiftedHom.equiv_mk₀

@[simp]

Depends on / 依赖: SmallShiftedHom, SmallShiftedHom.equiv_mk
-/
lemma mk₀_hom [HasDerivedCategory.{w'} C] (f : X ⟶ Y) :
    (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map f) := by
  apply SmallShiftedHom.equiv_mk₀

@[simp]
/--
lemma `mk₀_comp_mk₀` / 引理 `mk₀_comp_mk₀`

English:
lemma mk₀_comp_mk₀
  given: (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  let := HasDerivedCategory.standard C; ext; simp

@[simp]

中文:
引理 mk₀_comp_mk₀
  条件: (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  let := HasDerivedCategory.standard C; ext; simp

@[simp]

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, standard
-/
lemma mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk₀ f).comp (mk₀ g) (zero_add 0) = mk₀ (f ≫ g) := by
  let := HasDerivedCategory.standard C; ext; simp

@[simp]
/--
lemma `mk₀_comp_mk₀_assoc` / 引理 `mk₀_comp_mk₀_assoc`

English:
lemma mk₀_comp_mk₀_assoc
  given: (f : X ⟶ Y) (g : Y ⟶ Z) {n : Nat} (α : Ext Z T n)
  proof: by
  rw [← mk₀_comp_mk₀]; rw [comp_assoc]
  lia

中文:
引理 mk₀_comp_mk₀_assoc
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) {n : 自然数} (α : Ext Z T n)
  证明: by
  rw [← mk₀_comp_mk₀]; rw [comp_assoc]
  lia

Depends on / 依赖: comp_assoc
-/
lemma mk₀_comp_mk₀_assoc (f : X ⟶ Y) (g : Y ⟶ Z) {n : Nat} (α : Ext Z T n) :
    (mk₀ f).comp ((mk₀ g).comp α (zero_add n)) (zero_add n) =
      (mk₀ (f ≫ g)).comp α (zero_add n) := by
  rw [← mk₀_comp_mk₀]; rw [comp_assoc]
  lia


variable (X Y) in
/--
lemma `mk₀_bijective` / 引理 `mk₀_bijective`

English:
lemma mk₀_bijective
  statement: Function.Bijective (mk₀ (X := X) (Y := Y))
  proof: by
  let := HasDerivedCategory.standard C
  have h : (singleFunctor C 0).FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  let e : (X ⟶ Y) ≃ Ext X Y 0 :=
    (h.homEquiv.trans (ShiftedHom.homEquiv _ (by simp))).trans homEquiv.symm
  have he : e.toFun = mk₀ := by
    ext f : 1
    dsimp [e]


中文:
引理 mk₀_bijective
  结论: 函数.双射 (mk₀ (X := X) (Y := Y))
  证明: by
  let := HasDerivedCategory.standard C
  have h : (singleFunctor C 0).FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  let e : (X ⟶ Y) ≃ Ext X Y 0 :=
    (h.homEquiv.trans (ShiftedHom.homEquiv _ (by simp))).trans homEquiv.symm
  have he : e.toFun = mk₀ := by
    ext f : 1
    dsimp [e]


Depends on / 依赖: Equiv.apply_symm_apply, FullyFaithful, Functor, Functor.FullyFaithful.ofFullyFaithful, HasDerivedCategory, HasDerivedCategory.standard, ShiftedHom, ShiftedHom.homEquiv, SmallShiftedHom, SmallShiftedHom.equiv_mk, apply_symm_apply, bijective, e.bijective, e.toFun, h.homEquiv.trans, homEquiv, homEquiv.injective, homEquiv.symm, injective, ofFullyFaithful
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
/--
Definition of `homEquiv₀` / `homEquiv₀` 的定义

English:
definition homEquiv₀
  signature: : Ext X Y 0 ≃ (X ⟶ Y)
  body: (Equiv.ofBijective _ (mk₀_bijective X Y)).symm

@[simp]

中文:
定义 homEquiv₀
  签名: : Ext X Y 0 ≃ (X ⟶ Y)
  定义体: (Equiv.ofBijective _ (mk₀_bijective X Y)).symm

@[simp]

Depends on / 依赖: Equiv.ofBijective, ofBijective
-/
noncomputable def homEquiv₀ : Ext X Y 0 ≃ (X ⟶ Y) :=
  (Equiv.ofBijective _ (mk₀_bijective X Y)).symm

@[simp]
/--
lemma `mk₀_homEquiv₀_apply` / 引理 `mk₀_homEquiv₀_apply`

English:
lemma mk₀_homEquiv₀_apply
  given: (f : Ext X Y 0)
  proof: homEquiv₀.left_inv f

中文:
引理 mk₀_homEquiv₀_apply
  条件: (f : Ext X Y 0)
  证明: homEquiv₀.left_inv f

Depends on / 依赖: left_inv
-/
lemma mk₀_homEquiv₀_apply (f : Ext X Y 0) :
    mk₀ (homEquiv₀ f) = f :=
  homEquiv₀.left_inv f

variable {n : Nat}


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (Ext X Y n)
  body: letI := HasDerivedCategory.standard C
  homEquiv.addCommGroup

中文:
实例 :
  签名: 加法交换群 (Ext X Y n)
  定义体: letI := HasDerivedCategory.standard C
  homEquiv.addCommGroup

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, addCommGroup, homEquiv, homEquiv.addCommGroup, standard
-/
noncomputable instance : AddCommGroup (Ext X Y n) :=
  letI := HasDerivedCategory.standard C
  homEquiv.addCommGroup

/--
Definition of `hom'` / `hom'` 的定义

English:
abbreviation hom'
  signature: (α : Ext X Y n)
  body: HasDerivedCategory.standard C
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : Int) :=
  letI := HasDerivedCategory.standard C
  α.hom

中文:
缩写 hom'
  签名: (α : Ext X Y n)
  定义体: HasDerivedCategory.standard C
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : Int) :=
  letI := HasDerivedCategory.standard C
  α.hom

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, standard
-/
noncomputable abbrev hom' (α : Ext X Y n) :
    letI := HasDerivedCategory.standard C
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : Int) :=
  letI := HasDerivedCategory.standard C
  α.hom

/--
lemma `add_hom'` / 引理 `add_hom'`

English:
lemma add_hom'
  given: (α β : Ext X Y n)
  statement: (α + β).hom' = α.hom' + β.hom'
  proof: letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)

中文:
引理 add_hom'
  条件: (α β : Ext X Y n)
  结论: (α + β).hom' = α.hom' + β.hom'
  证明: letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)
-/
private lemma add_hom' (α β : Ext X Y n) : (α + β).hom' = α.hom' + β.hom' :=
  letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)

/--
lemma `neg_hom'` / 引理 `neg_hom'`

English:
lemma neg_hom'
  given: (α : Ext X Y n)
  statement: (-α).hom' = -α.hom'
  proof: letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)

中文:
引理 neg_hom'
  条件: (α : Ext X Y n)
  结论: (-α).hom' = -α.hom'
  证明: letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)
-/
private lemma neg_hom' (α : Ext X Y n) : (-α).hom' = -α.hom' :=
  letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)

variable (X Y n) in
/--
lemma `zero_hom'` / 引理 `zero_hom'`

English:
lemma zero_hom'
  statement: (0 : Ext X Y n).hom' = 0
  proof: letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)

@[simp]

中文:
引理 zero_hom'
  结论: (0 : Ext X Y n).hom' = 0
  证明: letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)

@[simp]
-/
private lemma zero_hom' : (0 : Ext X Y n).hom' = 0 :=
  letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)

@[simp]
/--
lemma `add_comp` / 引理 `add_comp`

English:
lemma add_comp
  given: (α₁ α₂ : Ext X Y n) {m : Nat} (β : Ext Y Z m) {p : Nat} (h : n + m = p)
  proof: by
  let := HasDerivedCategory.standard C; ext; simp [this, add_hom']

@[simp]

中文:
引理 add_comp
  条件: (α₁ α₂ : Ext X Y n) {m : 自然数} (β : Ext Y Z m) {p : 自然数} (h : n + m = p)
  证明: by
  let := HasDerivedCategory.standard C; ext; simp [this, add_hom']

@[simp]

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, add_hom, standard
-/
lemma add_comp (α₁ α₂ : Ext X Y n) {m : Nat} (β : Ext Y Z m) {p : Nat} (h : n + m = p) :
    (α₁ + α₂).comp β h = α₁.comp β h + α₂.comp β h := by
  let := HasDerivedCategory.standard C; ext; simp [this, add_hom']

@[simp]
/--
lemma `comp_add` / 引理 `comp_add`

English:
lemma comp_add
  given: (α : Ext X Y n) {m : Nat} (β₁ β₂ : Ext Y Z m) {p : Nat} (h : n + m = p)
  proof: by
  let := HasDerivedCategory.standard C; ext; simp [this, add_hom']

@[simp]

中文:
引理 comp_add
  条件: (α : Ext X Y n) {m : 自然数} (β₁ β₂ : Ext Y Z m) {p : 自然数} (h : n + m = p)
  证明: by
  let := HasDerivedCategory.standard C; ext; simp [this, add_hom']

@[simp]

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, add_hom, standard
-/
lemma comp_add (α : Ext X Y n) {m : Nat} (β₁ β₂ : Ext Y Z m) {p : Nat} (h : n + m = p) :
    α.comp (β₁ + β₂) h = α.comp β₁ h + α.comp β₂ h := by
  let := HasDerivedCategory.standard C; ext; simp [this, add_hom']

@[simp]
/--
lemma `neg_comp` / 引理 `neg_comp`

English:
lemma neg_comp
  given: (α : Ext X Y n) {m : Nat} (β : Ext Y Z m) {p : Nat} (h : n + m = p)
  proof: by
  let := HasDerivedCategory.standard C; ext; simp [this, neg_hom']

@[simp]

中文:
引理 neg_comp
  条件: (α : Ext X Y n) {m : 自然数} (β : Ext Y Z m) {p : 自然数} (h : n + m = p)
  证明: by
  let := HasDerivedCategory.standard C; ext; simp [this, neg_hom']

@[simp]

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, neg_hom, standard
-/
lemma neg_comp (α : Ext X Y n) {m : Nat} (β : Ext Y Z m) {p : Nat} (h : n + m = p) :
    (-α).comp β h = -α.comp β h := by
  let := HasDerivedCategory.standard C; ext; simp [this, neg_hom']

@[simp]
/--
lemma `comp_neg` / 引理 `comp_neg`

English:
lemma comp_neg
  given: (α : Ext X Y n) {m : Nat} (β : Ext Y Z m) {p : Nat} (h : n + m = p)
  proof: by
  let := HasDerivedCategory.standard C; ext; simp [this, neg_hom']

中文:
引理 comp_neg
  条件: (α : Ext X Y n) {m : 自然数} (β : Ext Y Z m) {p : 自然数} (h : n + m = p)
  证明: by
  let := HasDerivedCategory.standard C; ext; simp [this, neg_hom']

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, neg_hom, standard
-/
lemma comp_neg (α : Ext X Y n) {m : Nat} (β : Ext Y Z m) {p : Nat} (h : n + m = p) :
    α.comp (-β) h = -α.comp β h := by
  let := HasDerivedCategory.standard C; ext; simp [this, neg_hom']

variable (X n) in
@[simp]
/--
lemma `zero_comp` / 引理 `zero_comp`

English:
lemma zero_comp
  given: {m : Nat} (β : Ext Y Z m) (p : Nat) (h : n + m = p)
  proof: by
  let := HasDerivedCategory.standard C; ext; simp [this, zero_hom']

@[simp]

中文:
引理 zero_comp
  条件: {m : 自然数} (β : Ext Y Z m) (p : 自然数) (h : n + m = p)
  证明: by
  let := HasDerivedCategory.standard C; ext; simp [this, zero_hom']

@[simp]

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, standard, zero_hom
-/
lemma zero_comp {m : Nat} (β : Ext Y Z m) (p : Nat) (h : n + m = p) :
    (0 : Ext X Y n).comp β h = 0 := by
  let := HasDerivedCategory.standard C; ext; simp [this, zero_hom']

@[simp]
/--
lemma `comp_zero` / 引理 `comp_zero`

English:
lemma comp_zero
  given: (α : Ext X Y n) (Z : C) (m : Nat) (p : Nat) (h : n + m = p)
  proof: by
  let := HasDerivedCategory.standard C; ext; simp [this, zero_hom']

@[simp]

中文:
引理 comp_zero
  条件: (α : Ext X Y n) (Z : C) (m : 自然数) (p : 自然数) (h : n + m = p)
  证明: by
  let := HasDerivedCategory.standard C; ext; simp [this, zero_hom']

@[simp]

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, standard, zero_hom
-/
lemma comp_zero (α : Ext X Y n) (Z : C) (m : Nat) (p : Nat) (h : n + m = p) :
    α.comp (0 : Ext Y Z m) h = 0 := by
  let := HasDerivedCategory.standard C; ext; simp [this, zero_hom']

@[simp]
/--
lemma `mk₀_id_comp` / 引理 `mk₀_id_comp`

English:
lemma mk₀_id_comp
  given: (α : Ext X Y n)
  proof: by
  let := HasDerivedCategory.standard C; ext; simp

@[simp]

中文:
引理 mk₀_id_comp
  条件: (α : Ext X Y n)
  证明: by
  let := HasDerivedCategory.standard C; ext; simp

@[simp]

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, standard
-/
lemma mk₀_id_comp (α : Ext X Y n) :
    (mk₀ (𝟙 X)).comp α (zero_add n) = α := by
  let := HasDerivedCategory.standard C; ext; simp

@[simp]
/--
lemma `comp_mk₀_id` / 引理 `comp_mk₀_id`

English:
lemma comp_mk₀_id
  given: (α : Ext X Y n)
  proof: by
  let := HasDerivedCategory.standard C; ext; simp

中文:
引理 comp_mk₀_id
  条件: (α : Ext X Y n)
  证明: by
  let := HasDerivedCategory.standard C; ext; simp

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, standard
-/
lemma comp_mk₀_id (α : Ext X Y n) :
    α.comp (mk₀ (𝟙 Y)) (add_zero n) = α := by
  let := HasDerivedCategory.standard C; ext; simp

variable (X Y) in
@[simp]
/--
lemma `mk₀_zero` / 引理 `mk₀_zero`

English:
lemma mk₀_zero
  statement: mk₀ (0 : X ⟶ Y) = 0
  proof: by
  let := HasDerivedCategory.standard C; ext; simp [zero_hom']

中文:
引理 mk₀_zero
  结论: mk₀ (0 : X ⟶ Y) = 0
  证明: by
  let := HasDerivedCategory.standard C; ext; simp [zero_hom']

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, standard, zero_hom
-/
lemma mk₀_zero : mk₀ (0 : X ⟶ Y) = 0 := by
  let := HasDerivedCategory.standard C; ext; simp [zero_hom']

/--
lemma `mk₀_add` / 引理 `mk₀_add`

English:
lemma mk₀_add
  given: (f g : X ⟶ Y)
  statement: mk₀ (f + g) = mk₀ f + mk₀ g
  proof: by
  let := HasDerivedCategory.standard C; ext; simp [add_hom', ShiftedHom.mk₀]

中文:
引理 mk₀_add
  条件: (f g : X ⟶ Y)
  结论: mk₀ (f + g) = mk₀ f + mk₀ g
  证明: by
  let := HasDerivedCategory.standard C; ext; simp [add_hom', ShiftedHom.mk₀]

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, ShiftedHom, ShiftedHom.mk, add_hom, standard
-/
lemma mk₀_add (f g : X ⟶ Y) : mk₀ (f + g) = mk₀ f + mk₀ g := by
  let := HasDerivedCategory.standard C; ext; simp [add_hom', ShiftedHom.mk₀]

/-- The additive bijection `Ext X Y 0 ≃+ (X ⟶ Y)`. -/
@[simps! symm_apply]
/--
Definition of `addEquiv₀` / `addEquiv₀` 的定义

English:
definition addEquiv₀
  signature: : Ext X Y 0 ≃+ (X ⟶ Y) where
  body: homEquiv₀
  map_add' x y := homEquiv₀.symm.injective (by simp [mk₀_add])

@[simp]

中文:
定义 addEquiv₀
  签名: : Ext X Y 0 ≃+ (X ⟶ Y) where
  定义体: homEquiv₀
  map_add' x y := homEquiv₀.symm.injective (by simp [mk₀_add])

@[simp]
-/
noncomputable def addEquiv₀ : Ext X Y 0 ≃+ (X ⟶ Y) where
  toEquiv := homEquiv₀
  map_add' x y := homEquiv₀.symm.injective (by simp [mk₀_add])

@[simp]
/--
lemma `mk₀_addEquiv₀_apply` / 引理 `mk₀_addEquiv₀_apply`

English:
lemma mk₀_addEquiv₀_apply
  given: (f : Ext X Y 0)
  proof: addEquiv₀.left_inv f

@[simp]

中文:
引理 mk₀_addEquiv₀_apply
  条件: (f : Ext X Y 0)
  证明: addEquiv₀.left_inv f

@[simp]

Depends on / 依赖: left_inv
-/
lemma mk₀_addEquiv₀_apply (f : Ext X Y 0) :
    mk₀ (addEquiv₀ f) = f :=
  addEquiv₀.left_inv f

@[simp]
/--
lemma `mk₀_eq_zero_iff` / 引理 `mk₀_eq_zero_iff`

English:
lemma mk₀_eq_zero_iff
  given: {M N : C} (f : M ⟶ N)
  proof: Ext.addEquiv₀.symm.map_eq_zero_iff (x := f)

@[simp]

中文:
引理 mk₀_eq_zero_iff
  条件: {M N : C} (f : M ⟶ N)
  证明: Ext.addEquiv₀.symm.map_eq_zero_iff (x := f)

@[simp]

Depends on / 依赖: Ext.addEquiv, map_eq_zero_iff, symm.map_eq_zero_iff
-/
lemma mk₀_eq_zero_iff {M N : C} (f : M ⟶ N) :
    Ext.mk₀ f = 0 ↔ f = 0 :=
  Ext.addEquiv₀.symm.map_eq_zero_iff (x := f)

@[simp]
/--
lemma `mk₀_neg` / 引理 `mk₀_neg`

English:
lemma mk₀_neg
  given: (f : X ⟶ Y)
  proof: by
  let := HasDerivedCategory.standard C; ext; simp [neg_hom']

中文:
引理 mk₀_neg
  条件: (f : X ⟶ Y)
  证明: by
  let := HasDerivedCategory.standard C; ext; simp [neg_hom']

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, neg_hom, standard
-/
lemma mk₀_neg (f : X ⟶ Y) :
    mk₀ (-f) = -mk₀ f := by
  let := HasDerivedCategory.standard C; ext; simp [neg_hom']

section

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts in
/--
lemma `biprod_ext` / 引理 `biprod_ext`

English:
lemma biprod_ext
  statement: {X₁ X₂ : C} {α β : Ext (X₁ ⊞ X₂) Y n}
  proof: by
  let := HasDerivedCategory.standard C
  rw [Ext.ext_iff] at h₁ h₂ ⊢
  simp only [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp] at h₁ h₂
  apply BinaryCofan.IsColimit.hom_ext
    (isBinaryBilimitOfPreserves (singleFunctor C 0)
      (BinaryBiproduct.isBilimit X₁ X₂)).isColimit
  all_goals assumption

中文:
引理 biprod_ext
  结论: {X₁ X₂ : C} {α β : Ext (X₁ ⊞ X₂) Y n}
  证明: by
  let := HasDerivedCategory.standard C
  rw [Ext.ext_iff] at h₁ h₂ ⊢
  simp only [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp] at h₁ h₂
  apply BinaryCofan.IsColimit.hom_ext
    (isBinaryBilimitOfPreserves (singleFunctor C 0)
      (BinaryBiproduct.isBilimit X₁ X₂)).isColimit
  all_goals assumption

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isBilimit, BinaryCofan, BinaryCofan.IsColimit.hom_ext, Ext.ext_iff, HasDerivedCategory, HasDerivedCategory.standard, IsColimit, ShiftedHom, ShiftedHom.mk, all_goals, comp_hom, ext_iff, hom_ext, isBilimit, isBinaryBilimitOfPreserves, isColimit, singleFunctor, standard
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
/--
lemma `zero_hom` / 引理 `zero_hom`

English:
lemma zero_hom
  statement: (0 : Ext X Y n).hom = 0
  proof: by
  let β : Ext 0 Y n := 0
  have hβ : β.hom = 0 := by apply (Functor.map_isZero _ (isZero_zero C)).eq_of_src
  have : (0 : Ext X Y n) = (0 : Ext X 0 0).comp β (zero_add n) := by simp [β]
  rw [this]; rw [comp_hom]; rw [hβ]; rw [ShiftedHom.comp_zero]

@[simp]

中文:
引理 zero_hom
  结论: (0 : Ext X Y n).hom = 0
  证明: by
  let β : Ext 0 Y n := 0
  have hβ : β.hom = 0 := by apply (Functor.map_isZero _ (isZero_zero C)).eq_of_src
  have : (0 : Ext X Y n) = (0 : Ext X 0 0).comp β (zero_add n) := by simp [β]
  rw [this]; rw [comp_hom]; rw [hβ]; rw [ShiftedHom.comp_zero]

@[simp]

Depends on / 依赖: Functor, Functor.map_isZero, ShiftedHom, ShiftedHom.comp_zero, comp_hom, comp_zero, eq_of_src, isZero_zero, map_isZero, zero_add
-/
lemma zero_hom : (0 : Ext X Y n).hom = 0 := by
  let β : Ext 0 Y n := 0
  have hβ : β.hom = 0 := by apply (Functor.map_isZero _ (isZero_zero C)).eq_of_src
  have : (0 : Ext X Y n) = (0 : Ext X 0 0).comp β (zero_add n) := by simp [β]
  rw [this]; rw [comp_hom]; rw [hβ]; rw [ShiftedHom.comp_zero]

@[simp]
/--
lemma `add_hom` / 引理 `add_hom`

English:
lemma add_hom
  given: (α β : Ext X Y n)
  statement: (α + β).hom = α.hom + β.hom
  proof: by
  let α' : Ext (X ⊞ X) Y n := (mk₀ biprod.fst).comp α (zero_add n)
  let β' : Ext (X ⊞ X) Y n := (mk₀ biprod.snd).comp β (zero_add n)
  have eq₁ : α + β = (mk₀ (biprod.lift (𝟙 X) (𝟙 X))).comp (α' + β') (zero_add n) := by
    simp [α', β']
  have eq₂ : α' + β' = homEquiv.symm (α'.hom + β'.hom) := 

中文:
引理 add_hom
  条件: (α β : Ext X Y n)
  结论: (α + β).hom = α.hom + β.hom
  证明: by
  let α' : Ext (X ⊞ X) Y n := (mk₀ biprod.fst).comp α (zero_add n)
  let β' : Ext (X ⊞ X) Y n := (mk₀ biprod.snd).comp β (zero_add n)
  have eq₁ : α + β = (mk₀ (biprod.lift (𝟙 X) (𝟙 X))).comp (α' + β') (zero_add n) := by
    simp [α', β']
  have eq₂ : α' + β' = homEquiv.symm (α'.hom + β'.hom) := 

Depends on / 依赖: Equiv.apply_symm_apply, Functor, Functor.map_comp, ShiftedHom, ShiftedHom.comp_add, all_goals, apply_symm_apply, biprod, biprod.fst, biprod.lift, biprod.snd, biprod_ext, comp_add, comp_hom, homEquiv, homEquiv.symm, map_comp, zero_add
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
    rw [comp_hom]; rw [mk₀_hom]; rw [mk₀_hom]
    dsimp
    rw [ShiftedHom.mk₀_comp_mk₀_assoc]; rw [← Functor.map_comp]; rw [biprod.lift_fst]; rw [Functor.map_id]; rw [ShiftedHom.mk₀_id_comp]
  · dsimp [β']
    rw [comp_hom]; rw [mk₀_hom]; rw [mk₀_hom]
    dsimp
    rw [ShiftedHom.mk₀_comp_mk₀_assoc]; rw [← Functor.map_comp]; rw [biprod.lift_snd]; rw [Functor.map_id]; rw [ShiftedHom.mk₀_id_comp]

/--
lemma `neg_hom` / 引理 `neg_hom`

English:
lemma neg_hom
  given: (α : Ext X Y n)
  statement: (-α).hom = -α.hom
  proof: by
  rw [← add_right_inj α.hom]; rw [← add_hom]; rw [add_neg_cancel]; rw [add_neg_cancel]; rw [zero_hom]

中文:
引理 neg_hom
  条件: (α : Ext X Y n)
  结论: (-α).hom = -α.hom
  证明: by
  rw [← add_right_inj α.hom]; rw [← add_hom]; rw [add_neg_cancel]; rw [add_neg_cancel]; rw [zero_hom]

Depends on / 依赖: add_hom, add_neg_cancel, add_right_inj, zero_hom
-/
lemma neg_hom (α : Ext X Y n) : (-α).hom = -α.hom := by
  rw [← add_right_inj α.hom]; rw [← add_hom]; rw [add_neg_cancel]; rw [add_neg_cancel]; rw [zero_hom]

/--
Definition of `homAddEquiv` / `homAddEquiv` 的定义

English:
definition homAddEquiv
  signature: {n : Nat}
  body: homEquiv
  map_add' := by simp

@[simp]

中文:
定义 homAddEquiv
  签名: {n : 自然数}
  定义体: homEquiv
  map_add' := by simp

@[simp]

Depends on / 依赖: homEquiv
-/
noncomputable def homAddEquiv {n : Nat} :
    Ext.{w} X Y n ≃+
      ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : Int) where
  toEquiv := homEquiv
  map_add' := by simp

@[simp]
/--
lemma `homAddEquiv_apply` / 引理 `homAddEquiv_apply`

English:
lemma homAddEquiv_apply
  given: (α : Ext X Y n)
  statement: homAddEquiv α = α.hom
  proof: rfl

中文:
引理 homAddEquiv_apply
  条件: (α : Ext X Y n)
  结论: homAddEquiv α = α.hom
  证明: rfl
-/
lemma homAddEquiv_apply (α : Ext X Y n) : homAddEquiv α = α.hom := rfl

end

variable (X Y Z) in
/-- The composition of `Ext`, as a bilinear map. -/
@[simps!]
/--
Definition of `bilinearComp` / `bilinearComp` 的定义

English:
definition bilinearComp
  signature: (a b c : Nat) (h : a + b = c)
  body: AddMonoidHom.mk' (fun α => AddMonoidHom.mk' (fun β => α.comp β h) (by simp)) (by aesop)

中文:
定义 bilinearComp
  签名: (a b c : 自然数) (h : a + b = c)
  定义体: AddMonoidHom.mk' (fun α => AddMonoidHom.mk' (fun β => α.comp β h) (by simp)) (by aesop)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk
-/
noncomputable def bilinearComp (a b c : Nat) (h : a + b = c) :
    Ext X Y a ->+ Ext Y Z b ->+ Ext X Z c :=
  AddMonoidHom.mk' (fun α => AddMonoidHom.mk' (fun β => α.comp β h) (by simp)) (by aesop)

/--
Definition of `postcomp` / `postcomp` 的定义

English:
abbreviation postcomp
  signature: (β : Ext Y Z n) (X : C) {a b : Nat} (h : a + n = b)
  body: (bilinearComp X Y Z a n b h).flip β

中文:
缩写 postcomp
  签名: (β : Ext Y Z n) (X : C) {a b : 自然数} (h : a + n = b)
  定义体: (bilinearComp X Y Z a n b h).flip β

Depends on / 依赖: bilinearComp
-/
noncomputable abbrev postcomp (β : Ext Y Z n) (X : C) {a b : Nat} (h : a + n = b) :
    Ext X Y a ->+ Ext X Z b :=
  (bilinearComp X Y Z a n b h).flip β

/--
Definition of `precomp` / `precomp` 的定义

English:
abbreviation precomp
  signature: (α : Ext X Y n) (Z : C) {a b : Nat} (h : n + a = b)
  body: bilinearComp X Y Z n a b h α

中文:
缩写 precomp
  签名: (α : Ext X Y n) (Z : C) {a b : 自然数} (h : n + a = b)
  定义体: bilinearComp X Y Z n a b h α

Depends on / 依赖: bilinearComp
-/
noncomputable abbrev precomp (α : Ext X Y n) (Z : C) {a b : Nat} (h : n + a = b) :
    Ext Y Z a ->+ Ext X Z b :=
  bilinearComp X Y Z n a b h α

end Ext

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `extFunctor`. -/
@[simps]
/--
Definition of `extFunctorObj` / `extFunctorObj` 的定义

English:
definition extFunctorObj
  signature: (X : C) (n : Nat)
  body: AddCommGrpCat.of (Ext X Y n)
  map f := AddCommGrpCat.ofHom ((Ext.mk₀ f).postcomp _ (add_zero n))
  map_comp f f' := by
    ext α
    dsimp [AddCommGrpCat.ofHom]
    rw [← Ext.mk₀_comp_mk₀]
    symm
    apply Ext.comp_assoc
    lia

中文:
定义 extFunctorObj
  签名: (X : C) (n : 自然数)
  定义体: AddCommGrpCat.of (Ext X Y n)
  map f := AddCommGrpCat.ofHom ((Ext.mk₀ f).postcomp _ (add_zero n))
  map_comp f f' := by
    ext α
    dsimp [AddCommGrpCat.ofHom]
    rw [← Ext.mk₀_comp_mk₀]
    symm
    apply Ext.comp_assoc
    lia

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of
-/
noncomputable def extFunctorObj (X : C) (n : Nat) : C ⥤ AddCommGrpCat.{w} where
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
/--
Definition of `extFunctor` / `extFunctor` 的定义

English:
definition extFunctor
  signature: (n : Nat)
  body: extFunctorObj X.unop n
  map {X₁ X₂} f :=
    { app := fun Y => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun α => (Ext.mk₀ f.unop).comp α (zero_add _)) (by simp))
      naturality := fun {Y₁ Y₂} g => by
        ext α
        dsimp
        symm
        apply Ext.comp_assoc
        all_goals lia

中文:
定义 extFunctor
  签名: (n : 自然数)
  定义体: extFunctorObj X.unop n
  map {X₁ X₂} f :=
    { app := fun Y => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun α => (Ext.mk₀ f.unop).comp α (zero_add _)) (by simp))
      naturality := fun {Y₁ Y₂} g => by
        ext α
        dsimp
        symm
        apply Ext.comp_assoc
        all_goals lia

Depends on / 依赖: X.unop, extFunctorObj
-/
noncomputable def extFunctor (n : Nat) : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w} where
  obj X := extFunctorObj X.unop n
  map {X₁ X₂} f :=
    { app := fun Y => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun α => (Ext.mk₀ f.unop).comp α (zero_add _)) (by simp))
      naturality := fun {Y₁ Y₂} g => by
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

instance (X : C) (n : Nat) : (extFunctorObj X n).Additive where

instance (n : Nat) : (extFunctor (C := C) n).Additive where

/--
lemma `Ext.comp_sum` / 引理 `Ext.comp_sum`

English:
lemma Ext.comp_sum
  statement: {X Y Z : C} {p : Nat} (α : Ext X Y p) {ι : Type*} [Fintype ι] {q : Nat}
  proof: map_sum (α.precomp Z h) _ _

中文:
引理 Ext.comp_sum
  结论: {X Y Z : C} {p : 自然数} (α : Ext X Y p) {ι : 类型} [有限类型 ι] {q : 自然数}
  证明: map_sum (α.precomp Z h) _ _

Depends on / 依赖: map_sum, precomp
-/
lemma Ext.comp_sum {X Y Z : C} {p : Nat} (α : Ext X Y p) {ι : Type*} [Fintype ι] {q : Nat}
    (β : ι -> Ext Y Z q) {n : Nat} (h : p + q = n) :
    α.comp (∑ i, β i) h = ∑ i, α.comp (β i) h :=
  map_sum (α.precomp Z h) _ _

/--
lemma `Ext.sum_comp` / 引理 `Ext.sum_comp`

English:
lemma Ext.sum_comp
  statement: {X Y Z : C} {p : Nat} {ι : Type*} [Fintype ι] (α : ι -> Ext X Y p) {q : Nat}
  proof: map_sum (β.postcomp X h) _ _

中文:
引理 Ext.sum_comp
  结论: {X Y Z : C} {p : 自然数} {ι : 类型} [有限类型 ι] (α : ι -> Ext X Y p) {q : 自然数}
  证明: map_sum (β.postcomp X h) _ _

Depends on / 依赖: map_sum, postcomp
-/
lemma Ext.sum_comp {X Y Z : C} {p : Nat} {ι : Type*} [Fintype ι] (α : ι -> Ext X Y p) {q : Nat}
    (β : Ext Y Z q) {n : Nat} (h : p + q = n) :
    (∑ i, α i).comp β h = ∑ i, (α i).comp β h :=
  map_sum (β.postcomp X h) _ _

/--
lemma `Ext.mk₀_sum` / 引理 `Ext.mk₀_sum`

English:
lemma Ext.mk₀_sum
  given: {X Y : C} {ι : Type*} [Fintype ι] (f : ι -> (X ⟶ Y))
  proof: map_sum addEquiv₀.symm _ _

中文:
引理 Ext.mk₀_sum
  条件: {X Y : C} {ι : 类型} [有限类型 ι] (f : ι -> (X ⟶ Y))
  证明: map_sum addEquiv₀.symm _ _

Depends on / 依赖: map_sum
-/
lemma Ext.mk₀_sum {X Y : C} {ι : Type*} [Fintype ι] (f : ι -> (X ⟶ Y)) :
    mk₀ (∑ i, f i) = ∑ i, mk₀ (f i) :=
  map_sum addEquiv₀.symm _ _

/--
Definition of `Ext.biproductAddEquiv` / `Ext.biproductAddEquiv` 的定义

English:
definition Ext.biproductAddEquiv
  signature: {J : Type*} [Fintype J] {X : J -> C} {c : Bicone X}
  body: (Ext.mk₀ (c.ι i)).comp e (zero_add n)
  invFun e := ∑ (i : J), (Ext.mk₀ (c.π i)).comp (e i) (zero_add n)
  left_inv x := by
    simp only [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀]
    rw [← Ext.sum_comp]; rw [← Ext.mk₀_sum]; rw [IsBilimit.total hc]; rw [mk₀_id_comp]
  right_inv _ := by
    ext

中文:
定义 Ext.biproductAddEquiv
  签名: {J : 类型} [有限类型 J] {X : J -> C} {c : Bicone X}
  定义体: (Ext.mk₀ (c.ι i)).comp e (zero_add n)
  invFun e := ∑ (i : J), (Ext.mk₀ (c.π i)).comp (e i) (zero_add n)
  left_inv x := by
    simp only [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀]
    rw [← Ext.sum_comp]; rw [← Ext.mk₀_sum]; rw [IsBilimit.total hc]; rw [mk₀_id_comp]
  right_inv _ := by
    ext

Depends on / 依赖: Ext.mk, zero_add
-/
noncomputable def Ext.biproductAddEquiv {J : Type*} [Fintype J] {X : J -> C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : Nat) : Ext c.pt Y n ≃+ Π i, Ext (X i) Y n where
  toFun e i := (Ext.mk₀ (c.ι i)).comp e (zero_add n)
  invFun e := ∑ (i : J), (Ext.mk₀ (c.π i)).comp (e i) (zero_add n)
  left_inv x := by
    simp only [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀]
    rw [← Ext.sum_comp]; rw [← Ext.mk₀_sum]; rw [IsBilimit.total hc]; rw [mk₀_id_comp]
  right_inv _ := by
    ext i
    simp only [Ext.comp_sum, ← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀]
    rw [Finset.sum_eq_single i _ (by simp)]; rw [bicone_ι_π_self]; rw [mk₀_id_comp]
    intro _ _ hij
    rw [c.ι_π]; rw [dif_neg hij.symm]; rw [mk₀_zero]; rw [zero_comp]
  map_add' _ _ := by
    simp only [comp_add, Pi.add_def]

/--
Definition of `Ext.addEquivBiproduct` / `Ext.addEquivBiproduct` 的定义

English:
definition Ext.addEquivBiproduct
  signature: (X : C) {J : Type*} [Fintype J] {Y : J -> C} {c : Bicone Y}
  body: e.comp (Ext.mk₀ (c.π i)) (add_zero n)
  invFun e := ∑ (i : J), (e i).comp (Ext.mk₀ (c.ι i)) (add_zero n)
  left_inv _ := by
    simp only [comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, ← Ext.comp_sum,
      ← Ext.mk₀_sum, IsBilimit.total hc, comp_mk₀_id]
  right_inv _ := by
    ext i
    simp only [E

中文:
定义 Ext.addEquivBiproduct
  签名: (X : C) {J : 类型} [有限类型 J] {Y : J -> C} {c : Bicone Y}
  定义体: e.comp (Ext.mk₀ (c.π i)) (add_zero n)
  invFun e := ∑ (i : J), (e i).comp (Ext.mk₀ (c.ι i)) (add_zero n)
  left_inv _ := by
    simp only [comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, ← Ext.comp_sum,
      ← Ext.mk₀_sum, IsBilimit.total hc, comp_mk₀_id]
  right_inv _ := by
    ext i
    simp only [E

Depends on / 依赖: Ext.mk, add_zero, e.comp
-/
noncomputable def Ext.addEquivBiproduct (X : C) {J : Type*} [Fintype J] {Y : J -> C} {c : Bicone Y}
    (hc : c.IsBilimit) (n : Nat) : Ext X c.pt n ≃+ Π i, Ext X (Y i) n where
  toFun e i := e.comp (Ext.mk₀ (c.π i)) (add_zero n)
  invFun e := ∑ (i : J), (e i).comp (Ext.mk₀ (c.ι i)) (add_zero n)
  left_inv _ := by
    simp only [comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, ← Ext.comp_sum,
      ← Ext.mk₀_sum, IsBilimit.total hc, comp_mk₀_id]
  right_inv _ := by
    ext i
    simp only [Ext.sum_comp, comp_assoc_of_second_deg_zero, mk₀_comp_mk₀]
    rw [Finset.sum_eq_single i _ (by simp)]; rw [bicone_ι_π_self]; rw [comp_mk₀_id]
    intro _ _ hij
    rw [c.ι_π]; rw [dif_neg hij]; rw [mk₀_zero]; rw [comp_zero]
  map_add' _ _ := by
    simp only [add_comp, Pi.add_def]

end biproduct

/-- `Ext` commutes with binary biproducts on the first variable. -/
@[simps apply_fst apply_snd, simps -isSimp symm_apply]
/--
Definition of `Ext.biprodAddEquiv` / `Ext.biprodAddEquiv` 的定义

English:
definition Ext.biprodAddEquiv
  signature: {X₁ X₂ Y : C} {n : Nat}
  body: ⟨(mk₀ biprod.inl).comp e (zero_add n), (mk₀ biprod.inr).comp e (zero_add n)⟩
  invFun e := (mk₀ biprod.fst).comp e.1 (zero_add n) + (mk₀ biprod.snd).comp e.2 (zero_add n)
  left_inv _ := by
    simp only [mk₀_comp_mk₀_assoc, ← add_comp, ← mk₀_add, biprod.total, mk₀_id_comp]
  right_inv _ := by simp


中文:
定义 Ext.biprodAddEquiv
  签名: {X₁ X₂ Y : C} {n : 自然数}
  定义体: ⟨(mk₀ biprod.inl).comp e (zero_add n), (mk₀ biprod.inr).comp e (zero_add n)⟩
  invFun e := (mk₀ biprod.fst).comp e.1 (zero_add n) + (mk₀ biprod.snd).comp e.2 (zero_add n)
  left_inv _ := by
    simp only [mk₀_comp_mk₀_assoc, ← add_comp, ← mk₀_add, biprod.total, mk₀_id_comp]
  right_inv _ := by simp


Depends on / 依赖: biprod, biprod.inl, biprod.inr, zero_add
-/
noncomputable def Ext.biprodAddEquiv {X₁ X₂ Y : C} {n : Nat} :
    Ext (X₁ ⊞ X₂) Y n ≃+ Ext X₁ Y n × Ext X₂ Y n where
  toFun e := ⟨(mk₀ biprod.inl).comp e (zero_add n), (mk₀ biprod.inr).comp e (zero_add n)⟩
  invFun e := (mk₀ biprod.fst).comp e.1 (zero_add n) + (mk₀ biprod.snd).comp e.2 (zero_add n)
  left_inv _ := by
    simp only [mk₀_comp_mk₀_assoc, ← add_comp, ← mk₀_add, biprod.total, mk₀_id_comp]
  right_inv _ := by simp
  map_add' := by simp

/-- `Ext` commutes with binary biproducts on the second variable. -/
@[simps apply_fst apply_snd, simps -isSimp symm_apply]
/--
Definition of `Ext.addEquivBiprod` / `Ext.addEquivBiprod` 的定义

English:
definition Ext.addEquivBiprod
  signature: {X : C} {Y₁ Y₂ : C} {n : Nat}
  body: ⟨e.comp (mk₀ biprod.fst) (add_zero n), e.comp (mk₀ biprod.snd) (add_zero n)⟩
  invFun e := e.1.comp (mk₀ biprod.inl) (add_zero n) + e.2.comp (mk₀ biprod.inr) (add_zero n)
  left_inv e := by
    simp only [comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, ← comp_add, ← mk₀_add,
      biprod.total, comp_mk

中文:
定义 Ext.addEquivBiprod
  签名: {X : C} {Y₁ Y₂ : C} {n : 自然数}
  定义体: ⟨e.comp (mk₀ biprod.fst) (add_zero n), e.comp (mk₀ biprod.snd) (add_zero n)⟩
  invFun e := e.1.comp (mk₀ biprod.inl) (add_zero n) + e.2.comp (mk₀ biprod.inr) (add_zero n)
  left_inv e := by
    simp only [comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, ← comp_add, ← mk₀_add,
      biprod.total, comp_mk

Depends on / 依赖: add_zero, biprod, biprod.fst, biprod.snd, e.comp
-/
noncomputable def Ext.addEquivBiprod {X : C} {Y₁ Y₂ : C} {n : Nat} :
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

variable [HasExt.{w'} C] {X Y : C} {n : Nat}

/--
Definition of `chgUniv` / `chgUniv` 的定义

English:
definition chgUniv
  signature: : Ext.{w} X Y n ≃ Ext.{w'} X Y n
  body: SmallShiftedHom.chgUniv.{w', w}

中文:
定义 chgUniv
  签名: : Ext.{w} X Y n ≃ Ext.{w'} X Y n
  定义体: SmallShiftedHom.chgUniv.{w', w}

Depends on / 依赖: SmallShiftedHom, SmallShiftedHom.chgUniv, chgUniv
-/
noncomputable def chgUniv : Ext.{w} X Y n ≃ Ext.{w'} X Y n :=
  SmallShiftedHom.chgUniv.{w', w}

/--
lemma `homEquiv_chgUniv` / 引理 `homEquiv_chgUniv`

English:
lemma homEquiv_chgUniv
  given: [HasDerivedCategory.{w''} C] (e : Ext.{w} X Y n)
  proof: by
  apply SmallShiftedHom.equiv_chgUniv

中文:
引理 homEquiv_chgUniv
  条件: [HasDerivedCategory.{w''} C] (e : Ext.{w} X Y n)
  证明: by
  apply SmallShiftedHom.equiv_chgUniv

Depends on / 依赖: SmallShiftedHom, SmallShiftedHom.equiv_chgUniv, equiv_chgUniv
-/
lemma homEquiv_chgUniv [HasDerivedCategory.{w''} C] (e : Ext.{w} X Y n) :
    homEquiv.{w'', w'} (chgUniv.{w'} e) = homEquiv.{w'', w} e := by
  apply SmallShiftedHom.equiv_chgUniv

end Ext

end ChangeOfUniverse

end Abelian

open Abelian

variable (C) in
/--
lemma `hasExt_iff_small_ext` / 引理 `hasExt_iff_small_ext`

English:
lemma hasExt_iff_small_ext
  proof: by
  let := HasDerivedCategory.standard C
  simp only [hasExt_iff, small_congr Ext.homEquiv]
  constructor
  · intro h X Y n
    exact h X Y n (by simp)
  · intro h X Y n hn
    lift n to Nat using hn
    exact h X Y n

中文:
引理 hasExt_iff_small_ext
  证明: by
  let := HasDerivedCategory.standard C
  simp only [hasExt_iff, small_congr Ext.homEquiv]
  constructor
  · intro h X Y n
    exact h X Y n (by simp)
  · intro h X Y n hn
    lift n to Nat using hn
    exact h X Y n

Depends on / 依赖: Ext.homEquiv, HasDerivedCategory, HasDerivedCategory.standard, hasExt_iff, homEquiv, small_congr, standard
-/
lemma hasExt_iff_small_ext :
    HasExt.{w'} C ↔ forall (X Y : C) (n : Nat), Small.{w'} (Ext.{w} X Y n) := by
  let := HasDerivedCategory.standard C
  simp only [hasExt_iff, small_congr Ext.homEquiv]
  constructor
  · intro h X Y n
    exact h X Y n (by simp)
  · intro h X Y n hn
    lift n to Nat using hn
    exact h X Y n

end CategoryTheory
