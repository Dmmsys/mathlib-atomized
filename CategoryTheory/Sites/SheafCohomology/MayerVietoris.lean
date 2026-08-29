/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The Mayer-Vietoris exact sequence in sheaf cohomology

Let `C` be a category equipped with a Grothendieck topology `J`.
Let `S : J.MayerVietorisSquare` be a Mayer-Vietoris square for `J`.
Let `F` be an abelian sheaf on `(C, J)`.

In this file, we obtain a long exact Mayer-Vietoris sequence:

`... ⟶ H^n(S.X₄, F) ⟶ H^n(S.X₂, F) ⊞ H^n(S.X₃, F) ⟶ H^n(S.X₁, F) ⟶ H^{n + 1}(S.X₄, F) ⟶ ...`

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Opposite Limits Abelian

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

namespace GrothendieckTopology.MayerVietorisSquare

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})

/--
Definition of `toBiprod` / `toBiprod` 的定义

English:
definition toBiprod
  signature: (n : Nat)
  body: biprod.lift ((F.cohomologyPresheaf n).map S.f₂₄.op)
      ((F.cohomologyPresheaf n).map S.f₃₄.op)

中文:
定义 toBiprod
  签名: (n : 自然数)
  定义体: biprod.lift ((F.cohomologyPresheaf n).map S.f₂₄.op)
      ((F.cohomologyPresheaf n).map S.f₃₄.op)

Depends on / 依赖: F.cohomologyPresheaf, biprod, biprod.lift, cohomologyPresheaf
-/
noncomputable def toBiprod (n : Nat) :
    F.H' n S.X₄ ⟶ F.H' n S.X₂ ⊞ F.H' n S.X₃ :=
  biprod.lift ((F.cohomologyPresheaf n).map S.f₂₄.op)
      ((F.cohomologyPresheaf n).map S.f₃₄.op)

/--
lemma `toBiprod_apply` / 引理 `toBiprod_apply`

English:
lemma toBiprod_apply
  given: {n : Nat} (y : F.H' n S.X₄)
  proof: by
  apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
  dsimp [toBiprod]
  ext
  · rw [Iso.addCommGroupIsoToAddEquiv_apply,
      Iso.addCommGroupIsoToAddEquiv_apply,
      ← AddCommGrpCat.biprodIsoProd_inv_comp_fst_apply,
      Iso.hom_inv_id_apply, ← ConcreteCategory.com

中文:
引理 toBiprod_apply
  条件: {n : 自然数} (y : F.H' n S.X₄)
  证明: by
  apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
  dsimp [toBiprod]
  ext
  · rw [Iso.addCommGroupIsoToAddEquiv_apply,
      Iso.addCommGroupIsoToAddEquiv_apply,
      ← AddCommGrpCat.biprodIsoProd_inv_comp_fst_apply,
      Iso.hom_inv_id_apply, ← ConcreteCategory.com

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.biprodIsoProd, AddCommGrpCat.biprodIsoProd_inv_comp_fst_apply, AddCommGrpCat.biprodIsoProd_inv_comp_snd_apply, ConcreteCategory, ConcreteCategory.comp_ap, ConcreteCategory.comp_apply, Iso.addCommGroupIsoToAddEquiv_apply, Iso.hom_inv_id_apply, Iso.inv_hom_id_apply, addCommGroupIsoToAddEquiv, addCommGroupIsoToAddEquiv.injective, addCommGroupIsoToAddEquiv_apply, biprod, biprod.lift_fst, biprodIsoProd, biprodIsoProd_inv_comp_fst_apply, biprodIsoProd_inv_comp_snd_apply, comp_ap, comp_apply
-/
lemma toBiprod_apply {n : Nat} (y : F.H' n S.X₄) :
    S.toBiprod F n y = (AddCommGrpCat.biprodIsoProd _ _).inv
      ⟨(F.cohomologyPresheaf n).map S.f₂₄.op y,
        (F.cohomologyPresheaf n).map S.f₃₄.op y⟩ := by
  apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
  dsimp [toBiprod]
  ext
  · rw [Iso.addCommGroupIsoToAddEquiv_apply,
      Iso.addCommGroupIsoToAddEquiv_apply,
      ← AddCommGrpCat.biprodIsoProd_inv_comp_fst_apply,
      Iso.hom_inv_id_apply, ← ConcreteCategory.comp_apply,
      biprod.lift_fst, Iso.inv_hom_id_apply]
  · rw [Iso.addCommGroupIsoToAddEquiv_apply,
      Iso.addCommGroupIsoToAddEquiv_apply,
      ← AddCommGrpCat.biprodIsoProd_inv_comp_snd_apply,
      Iso.hom_inv_id_apply, ← ConcreteCategory.comp_apply,
      biprod.lift_snd, Iso.inv_hom_id_apply]

/--
Definition of `fromBiprod` / `fromBiprod` 的定义

English:
definition fromBiprod
  signature: (n : Nat)
  body: biprod.desc ((F.cohomologyPresheaf n).map S.f₁₂.op)
      (-(F.cohomologyPresheaf n).map S.f₁₃.op)

@[reassoc (attr := simp)]

中文:
定义 fromBiprod
  签名: (n : 自然数)
  定义体: biprod.desc ((F.cohomologyPresheaf n).map S.f₁₂.op)
      (-(F.cohomologyPresheaf n).map S.f₁₃.op)

@[reassoc (attr := simp)]

Depends on / 依赖: F.cohomologyPresheaf, biprod, biprod.desc, cohomologyPresheaf
-/
noncomputable def fromBiprod (n : Nat) :
    F.H' n S.X₂ ⊞ F.H' n S.X₃ ⟶ F.H' n S.X₁ :=
  biprod.desc ((F.cohomologyPresheaf n).map S.f₁₂.op)
      (-(F.cohomologyPresheaf n).map S.f₁₃.op)

@[reassoc (attr := simp)]
/--
lemma `toBiprod_fromBiprod` / 引理 `toBiprod_fromBiprod`

English:
lemma toBiprod_fromBiprod
  given: (n : Nat)
  statement: S.toBiprod F n ≫ S.fromBiprod F n = 0
  proof: by
  simp only [toBiprod, fromBiprod, biprod.lift_desc, Preadditive.comp_neg,
    ← sub_eq_add_neg, sub_eq_zero, ← Functor.map_comp, ← op_comp, S.toSquare.fac]

中文:
引理 toBiprod_fromBiprod
  条件: (n : 自然数)
  结论: S.toBiprod F n ≫ S.fromBiprod F n = 0
  证明: by
  simp only [toBiprod, fromBiprod, biprod.lift_desc, Preadditive.comp_neg,
    ← sub_eq_add_neg, sub_eq_zero, ← Functor.map_comp, ← op_comp, S.toSquare.fac]

Depends on / 依赖: Functor, Functor.map_comp, Preadditive, Preadditive.comp_neg, S.toSquare.fac, biprod, biprod.lift_desc, comp_neg, fromBiprod, lift_desc, map_comp, op_comp, sub_eq_add_neg, sub_eq_zero, toBiprod, toSquare
-/
lemma toBiprod_fromBiprod (n : Nat) : S.toBiprod F n ≫ S.fromBiprod F n = 0 := by
  simp only [toBiprod, fromBiprod, biprod.lift_desc, Preadditive.comp_neg,
    ← sub_eq_add_neg, sub_eq_zero, ← Functor.map_comp, ← op_comp, S.toSquare.fac]

/--
lemma `fromBiprod_biprodIsoProd_inv_apply` / 引理 `fromBiprod_biprodIsoProd_inv_apply`

English:
lemma fromBiprod_biprodIsoProd_inv_apply
  statement: {n : Nat}
  proof: by
  dsimp [fromBiprod]
  rw [← ConcreteCategory.comp_apply]
  simp [AddCommGrpCat.biprodIsoProd_inv_comp_desc, sub_eq_add_neg]

中文:
引理 fromBiprod_biprodIsoProd_inv_apply
  结论: {n : 自然数}
  证明: by
  dsimp [fromBiprod]
  rw [← ConcreteCategory.comp_apply]
  simp [AddCommGrpCat.biprodIsoProd_inv_comp_desc, sub_eq_add_neg]

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.biprodIsoProd_inv_comp_desc, ConcreteCategory, ConcreteCategory.comp_apply, biprodIsoProd_inv_comp_desc, comp_apply, fromBiprod, sub_eq_add_neg
-/
lemma fromBiprod_biprodIsoProd_inv_apply {n : Nat}
    (y₁ : F.H' n S.X₂) (y₂ : F.H' n S.X₃) :
    S.fromBiprod F n ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨y₁, y₂⟩) =
      (F.cohomologyPresheaf n).map S.f₁₂.op y₁ - (F.cohomologyPresheaf n).map S.f₁₃.op y₂ := by
  dsimp [fromBiprod]
  rw [← ConcreteCategory.comp_apply]
  simp [AddCommGrpCat.biprodIsoProd_inv_comp_desc, sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] toBiprod_apply in
/--
lemma `biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply` / 引理 `biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply`

English:
lemma biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply
  proof: Ext.biprodAddEquiv.injective (by cat_disch)

中文:
引理 biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply
  证明: Ext.biprodAddEquiv.injective (by cat_disch)

Depends on / 依赖: Ext.biprodAddEquiv.injective, biprodAddEquiv, cat_disch, injective
-/
lemma biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply
    {n : Nat} (x : F.H' n S.X₄) :
    Ext.biprodAddEquiv.symm ((AddCommGrpCat.biprodIsoProd _ _).hom (S.toBiprod F n x)) =
      (Ext.mk₀ S.shortComplex.g).comp x (zero_add n) :=
  Ext.biprodAddEquiv.injective (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] sub_eq_add_neg in
/--
lemma `mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom` / 引理 `mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom`

English:
lemma mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom
  proof: by
  obtain ⟨⟨x₂, x₃⟩, rfl⟩ :=
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective x
  dsimp
  rw [Ext.biprodAddEquiv_symm_apply]; rw [Iso.addCommGroupIsoToAddEquiv_symm_apply]; rw [fromBiprod_biprodIsoProd_inv_apply]
  cat_disch

中文:
引理 mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom
  证明: by
  obtain ⟨⟨x₂, x₃⟩, rfl⟩ :=
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective x
  dsimp
  rw [Ext.biprodAddEquiv_symm_apply]; rw [Iso.addCommGroupIsoToAddEquiv_symm_apply]; rw [fromBiprod_biprodIsoProd_inv_apply]
  cat_disch

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.biprodIsoProd, Ext.biprodAddEquiv_symm_apply, Iso.addCommGroupIsoToAddEquiv_symm_apply, addCommGroupIsoToAddEquiv, addCommGroupIsoToAddEquiv.symm.surjective, addCommGroupIsoToAddEquiv_symm_apply, biprodAddEquiv_symm_apply, biprodIsoProd, cat_disch, fromBiprod_biprodIsoProd_inv_apply, surjective
-/
lemma mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom
    {n : Nat} (x : ↑(F.H' n S.X₂ ⊞ F.H' n S.X₃)) :
    (Ext.mk₀ S.shortComplex.f).comp
      (Ext.biprodAddEquiv.symm ((AddCommGrpCat.biprodIsoProd _ _).hom x)) (zero_add n) =
    (S.fromBiprod F n x) := by
  obtain ⟨⟨x₂, x₃⟩, rfl⟩ :=
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective x
  dsimp
  rw [Ext.biprodAddEquiv_symm_apply]; rw [Iso.addCommGroupIsoToAddEquiv_symm_apply]; rw [fromBiprod_biprodIsoProd_inv_apply]
  cat_disch

variable (n₀ n₁ : Nat) (h : n₀ + 1 = n₁)

/--
Definition of `δ` / `δ` 的定义

English:
definition δ
  signature: :
  body: AddCommGrpCat.ofHom (S.shortComplex_shortExact.extClass.precomp _ (by omega))

中文:
定义 δ
  签名: :
  定义体: AddCommGrpCat.ofHom (S.shortComplex_shortExact.extClass.precomp _ (by omega))

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.ofHom, S.shortComplex_shortExact.extClass.precomp, extClass, precomp, shortComplex_shortExact
-/
noncomputable def δ :
    F.H' n₀ S.X₁ ⟶ F.H' n₁ S.X₄ :=
  AddCommGrpCat.ofHom (S.shortComplex_shortExact.extClass.precomp _ (by omega))

open ComposableArrows

/--
Definition of `sequence` / `sequence` 的定义

English:
abbreviation sequence
  signature: : ComposableArrows AddCommGrpCat.{w} 5
  body: mk₅ (S.toBiprod F n₀) (S.fromBiprod F n₀) (S.δ F n₀ n₁ h)
    (S.toBiprod F n₁) (S.fromBiprod F n₁)

中文:
缩写 sequence
  签名: : ComposableArrows 加法交换群范畴.{w} 5
  定义体: mk₅ (S.toBiprod F n₀) (S.fromBiprod F n₀) (S.δ F n₀ n₁ h)
    (S.toBiprod F n₁) (S.fromBiprod F n₁)

Depends on / 依赖: S.fromBiprod, S.toBiprod, fromBiprod, toBiprod
-/
noncomputable abbrev sequence : ComposableArrows AddCommGrpCat.{w} 5 :=
  mk₅ (S.toBiprod F n₀) (S.fromBiprod F n₀) (S.δ F n₀ n₁ h)
    (S.toBiprod F n₁) (S.fromBiprod F n₁)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sequenceIso` / `sequenceIso` 的定义

English:
definition sequenceIso
  signature: : S.sequence F n₀ n₁ h ≅
  body: isoMk₅ (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans (Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _) (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans (Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _)
    (by ext; apply biprodAddEquiv_symm_biprodIsoProd_hom_

中文:
定义 sequenceIso
  签名: : S.sequence F n₀ n₁ h ≅
  定义体: isoMk₅ (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans (Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _) (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans (Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _)
    (by ext; apply biprodAddEquiv_symm_biprodIsoProd_hom_

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.biprodIsoProd, Ext.biprodAddEquiv.symm, Iso.refl, biprodAddEquiv, biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply, biprodIsoProd, comp_id, id_comp, toAddCommGrpIso
-/
noncomputable def sequenceIso : S.sequence F n₀ n₁ h ≅
    Ext.contravariantSequence S.shortComplex_shortExact F n₀ n₁ (by omega) :=
  isoMk₅ (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans (Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _) (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans (Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _)
    (by ext; apply biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom)
    (by dsimp; rw [comp_id, id_comp]; rfl)
    (by ext; apply biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom)

/--
lemma `sequence_exact` / 引理 `sequence_exact`

English:
lemma sequence_exact
  statement: (S.sequence F n₀ n₁ h).Exact
  proof: exact_of_iso (S.sequenceIso F n₀ n₁ h).symm (Ext.contravariantSequence_exact _ _ _ _ _)

@[reassoc (attr := simp)]

中文:
引理 sequence_exact
  结论: (S.sequence F n₀ n₁ h).正合
  证明: exact_of_iso (S.sequenceIso F n₀ n₁ h).symm (Ext.contravariantSequence_exact _ _ _ _ _)

@[reassoc (attr := simp)]

Depends on / 依赖: Ext.contravariantSequence_exact, S.sequenceIso, contravariantSequence_exact, exact_of_iso, sequenceIso
-/
lemma sequence_exact : (S.sequence F n₀ n₁ h).Exact :=
  exact_of_iso (S.sequenceIso F n₀ n₁ h).symm (Ext.contravariantSequence_exact _ _ _ _ _)

@[reassoc (attr := simp)]
/--
lemma `δ_toBiprod` / 引理 `δ_toBiprod`

English:
lemma δ_toBiprod
  statement: S.δ F n₀ n₁ h ≫ S.toBiprod F n₁ = 0
  proof: (S.sequence_exact F n₀ n₁ h).zero 2

@[reassoc (attr := simp)]

中文:
引理 δ_toBiprod
  结论: S.δ F n₀ n₁ h ≫ S.toBiprod F n₁ = 0
  证明: (S.sequence_exact F n₀ n₁ h).zero 2

@[reassoc (attr := simp)]

Depends on / 依赖: S.sequence_exact, sequence_exact
-/
lemma δ_toBiprod : S.δ F n₀ n₁ h ≫ S.toBiprod F n₁ = 0 :=
  (S.sequence_exact F n₀ n₁ h).zero 2

@[reassoc (attr := simp)]
/--
lemma `fromBiprod_δ` / 引理 `fromBiprod_δ`

English:
lemma fromBiprod_δ
  statement: S.fromBiprod F n₀ ≫ S.δ F n₀ n₁ h = 0
  proof: (S.sequence_exact F n₀ n₁ h).zero 1

中文:
引理 fromBiprod_δ
  结论: S.fromBiprod F n₀ ≫ S.δ F n₀ n₁ h = 0
  证明: (S.sequence_exact F n₀ n₁ h).zero 1

Depends on / 依赖: S.sequence_exact, sequence_exact
-/
lemma fromBiprod_δ : S.fromBiprod F n₀ ≫ S.δ F n₀ n₁ h = 0 :=
  (S.sequence_exact F n₀ n₁ h).zero 1

end GrothendieckTopology.MayerVietorisSquare

end CategoryTheory
