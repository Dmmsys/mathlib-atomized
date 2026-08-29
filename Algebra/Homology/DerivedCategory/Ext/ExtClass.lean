/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# The Ext class of a short exact sequence

In this file, given a short exact short complex `S : ShortComplex C`
in an abelian category, we construct the associated class in
`Ext S.X₃ S.X₁ 1`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

open Localization Limits ZeroObject DerivedCategory Pretriangulated Abelian

namespace ShortComplex

variable (S : ShortComplex C)

/--
lemma `ext_mk₀_f_comp_ext_mk₀_g` / 引理 `ext_mk₀_f_comp_ext_mk₀_g`

English:
lemma ext_mk₀_f_comp_ext_mk₀_g
  statement: (Ext.mk₀ S.f).comp (Ext.mk₀ S.g) (zero_add 0) = 0
  proof: by simp

中文:
引理 ext_mk₀_f_comp_ext_mk₀_g
  结论: (Ext.mk₀ S.f).comp (Ext.mk₀ S.g) (zero_add 0) = 0
  证明: by simp
-/
lemma ext_mk₀_f_comp_ext_mk₀_g : (Ext.mk₀ S.f).comp (Ext.mk₀ S.g) (zero_add 0) = 0 := by simp

namespace ShortExact

variable {S}
variable (hS : S.ShortExact)

section

local notation "W" => HomologicalComplex.quasiIso C (ComplexShape.up Int)
local notation "S'" => S.map (CochainComplex.singleFunctor C 0)
local notation "hS'" => hS.map_of_exact (HomologicalComplex.single _ _ _)
local notation "K" => CochainComplex.mappingCone (ShortComplex.f S')
local notation "qis" => CochainComplex.mappingCone.descShortComplex S'
local notation "hqis" => CochainComplex.mappingCone.quasiIso_descShortComplex hS'
local notation "δ" => Triangle.mor₃ (CochainComplex.mappingCone.triangle (ShortComplex.f S'))

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSmallLocalizedShiftedHom.{w} W Int (S').X₃ (S').X₁
  body: by
  dsimp
  infer_instance

中文:
实例 :
  签名: HasSmallLocalizedShiftedHom.{w} W 整数 (S').X₃ (S').X₁
  定义体: by
  dsimp
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : HasSmallLocalizedShiftedHom.{w} W Int (S').X₃ (S').X₁ := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
include hS in
/--
lemma `hasSmallLocalizedHom_S'_X₃_K` / 引理 `hasSmallLocalizedHom_S'_X₃_K`

English:
lemma hasSmallLocalizedHom_S'_X₃_K
  proof: by
  rw [Localization.hasSmallLocalizedHom_iff_target W (S').X₃ qis hqis]
  dsimp
  apply Localization.hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ (M := Int)

中文:
引理 hasSmallLocalizedHom_S'_X₃_K
  证明: by
  rw [Localization.hasSmallLocalizedHom_iff_target W (S').X₃ qis hqis]
  dsimp
  apply Localization.hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ (M := Int)
-/
private lemma hasSmallLocalizedHom_S'_X₃_K :
    HasSmallLocalizedHom.{w} W (S').X₃ K := by
  rw [Localization.hasSmallLocalizedHom_iff_target W (S').X₃ qis hqis]
  dsimp
  apply Localization.hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ (M := Int)

set_option backward.privateInPublic true in
include hS in
/--
lemma `hasSmallLocalizedShiftedHom_K_S'_X₁` / 引理 `hasSmallLocalizedShiftedHom_K_S'_X₁`

English:
lemma hasSmallLocalizedShiftedHom_K_S'_X₁
  proof: by
  rw [Localization.hasSmallLocalizedShiftedHom_iff_source.{w} W Int qis hqis (S').X₁]
  infer_instance

中文:
引理 hasSmallLocalizedShiftedHom_K_S'_X₁
  证明: by
  rw [Localization.hasSmallLocalizedShiftedHom_iff_source.{w} W Int qis hqis (S').X₁]
  infer_instance
-/
private lemma hasSmallLocalizedShiftedHom_K_S'_X₁ :
    HasSmallLocalizedShiftedHom.{w} W Int K (S').X₁ := by
  rw [Localization.hasSmallLocalizedShiftedHom_iff_source.{w} W Int qis hqis (S').X₁]
  infer_instance

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `extClass` / `extClass` 的定义

English:
definition extClass
  signature: : Ext.{w} S.X₃ S.X₁ 1
  body: by
  have := hS.hasSmallLocalizedHom_S'_X₃_K
  have := hS.hasSmallLocalizedShiftedHom_K_S'_X₁
  change SmallHom W (S').X₃ ((S').X₁⟦(1 : Int)⟧)
  exact (SmallHom.mkInv qis hqis).comp (SmallHom.mk W δ)

中文:
定义 extClass
  签名: : Ext.{w} S.X₃ S.X₁ 1
  定义体: by
  have := hS.hasSmallLocalizedHom_S'_X₃_K
  have := hS.hasSmallLocalizedShiftedHom_K_S'_X₁
  change SmallHom W (S').X₃ ((S').X₁⟦(1 : Int)⟧)
  exact (SmallHom.mkInv qis hqis).comp (SmallHom.mk W δ)

Depends on / 依赖: SmallHom, SmallHom.mk, SmallHom.mkInv, hS.hasSmallLocalizedHom_S, hS.hasSmallLocalizedShiftedHom_K_S, hasSmallLocalizedHom_S, hasSmallLocalizedShiftedHom_K_S
-/
noncomputable def extClass : Ext.{w} S.X₃ S.X₁ 1 := by
  have := hS.hasSmallLocalizedHom_S'_X₃_K
  have := hS.hasSmallLocalizedShiftedHom_K_S'_X₁
  change SmallHom W (S').X₃ ((S').X₁⟦(1 : Int)⟧)
  exact (SmallHom.mkInv qis hqis).comp (SmallHom.mk W δ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `extClass_hom` / 引理 `extClass_hom`

English:
lemma extClass_hom
  given: [HasDerivedCategory.{w'} C]
  statement: hS.extClass.hom = hS.singleδ
  proof: by
  change SmallShiftedHom.equiv W Q hS.extClass = _
  dsimp [extClass, SmallShiftedHom.equiv]
  erw [SmallHom.equiv_comp]
  rw [SmallHom.equiv_mkInv]; rw [SmallHom.equiv_mk]
  dsimp [-Q_obj_single_obj, singleδ, triangleOfSESδ]
  rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [singleFunctorsPostcompQIso_hom_hom]; rw [singleFunctorsPostcompQIso_inv_hom]; rw [NatTrans.id_app]; rw [Category.id_comp]; rw [NatTrans.id_app]
  simp only [SingleFunctors.postcomp, Functor.comp_obj]
  unfold CochainComplex.singleFunctors
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl

中文:
引理 extClass_hom
  条件: [HasDerivedCategory.{w'} C]
  结论: hS.extClass.hom = hS.singleδ
  证明: by
  change SmallShiftedHom.equiv W Q hS.extClass = _
  dsimp [extClass, SmallShiftedHom.equiv]
  erw [SmallHom.equiv_comp]
  rw [SmallHom.equiv_mkInv]; rw [SmallHom.equiv_mk]
  dsimp [-Q_obj_single_obj, singleδ, triangleOfSESδ]
  rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [singleFunctorsPostcompQIso_hom_hom]; rw [singleFunctorsPostcompQIso_inv_hom]; rw [NatTrans.id_app]; rw [Category.id_comp]; rw [NatTrans.id_app]
  simp only [SingleFunctors.postcomp, Functor.comp_obj]
  unfold CochainComplex.singleFunctors
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl

Depends on / 依赖: Category, Category.assoc, Category.id_comp, CochainCo, Functor, Functor.comp_obj, NatTrans, NatTrans.id_app, Q_obj_single_obj, SingleFunctors, SingleFunctors.postcomp, SmallHom, SmallHom.equiv_comp, SmallHom.equiv_mk, SmallHom.equiv_mkInv, SmallShiftedHom, SmallShiftedHom.equiv, comp_obj, equiv_comp, equiv_mk
-/
lemma extClass_hom [HasDerivedCategory.{w'} C] : hS.extClass.hom = hS.singleδ := by
  change SmallShiftedHom.equiv W Q hS.extClass = _
  dsimp [extClass, SmallShiftedHom.equiv]
  erw [SmallHom.equiv_comp]
  rw [SmallHom.equiv_mkInv]; rw [SmallHom.equiv_mk]
  dsimp [-Q_obj_single_obj, singleδ, triangleOfSESδ]
  rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [singleFunctorsPostcompQIso_hom_hom]; rw [singleFunctorsPostcompQIso_inv_hom]; rw [NatTrans.id_app]; rw [Category.id_comp]; rw [NatTrans.id_app]
  simp only [SingleFunctors.postcomp, Functor.comp_obj]
  unfold CochainComplex.singleFunctors
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl

end

@[simp]
/--
lemma `comp_extClass` / 引理 `comp_extClass`

English:
lemma comp_extClass
  statement: (Ext.mk₀ S.g).comp hS.extClass (zero_add 1) = 0
  proof: by
  let := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom, Ext.zero_hom,
    ShiftedHom.mk₀_comp]
  exact comp_distTriang_mor_zero₂₃ _ hS.singleTriangle_distinguished

@[simp]

中文:
引理 comp_extClass
  结论: (Ext.mk₀ S.g).comp hS.extClass (zero_add 1) = 0
  证明: by
  let := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom, Ext.zero_hom,
    ShiftedHom.mk₀_comp]
  exact comp_distTriang_mor_zero₂₃ _ hS.singleTriangle_distinguished

@[simp]

Depends on / 依赖: Ext.comp_hom, Ext.mk, Ext.zero_hom, HasDerivedCategory, HasDerivedCategory.standard, ShiftedHom, ShiftedHom.mk, comp_hom, extClass_hom, hS.singleTriangle_distinguished, singleTriangle_distinguished, standard, zero_hom
-/
lemma comp_extClass : (Ext.mk₀ S.g).comp hS.extClass (zero_add 1) = 0 := by
  let := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom, Ext.zero_hom,
    ShiftedHom.mk₀_comp]
  exact comp_distTriang_mor_zero₂₃ _ hS.singleTriangle_distinguished

@[simp]
/--
lemma `comp_extClass_assoc` / 引理 `comp_extClass_assoc`

English:
lemma comp_extClass_assoc
  given: {Y : C} {n : Nat} (γ : Ext S.X₁ Y n) {n' : Nat} (h : 1 + n = n')
  proof: by
  rw [← Ext.comp_assoc (a₁₂ := 1) _ _ _ (by lia) (by lia) (by lia)]; rw [comp_extClass]; rw [Ext.zero_comp]

@[simp]

中文:
引理 comp_extClass_assoc
  条件: {Y : C} {n : 自然数} (γ : Ext S.X₁ Y n) {n' : 自然数} (h : 1 + n = n')
  证明: by
  rw [← Ext.comp_assoc (a₁₂ := 1) _ _ _ (by lia) (by lia) (by lia)]; rw [comp_extClass]; rw [Ext.zero_comp]

@[simp]

Depends on / 依赖: Ext.comp_assoc, Ext.zero_comp, comp_assoc, comp_extClass, zero_comp
-/
lemma comp_extClass_assoc {Y : C} {n : Nat} (γ : Ext S.X₁ Y n) {n' : Nat} (h : 1 + n = n') :
    (Ext.mk₀ S.g).comp (hS.extClass.comp γ h) (zero_add n') = 0 := by
  rw [← Ext.comp_assoc (a₁₂ := 1) _ _ _ (by lia) (by lia) (by lia)]; rw [comp_extClass]; rw [Ext.zero_comp]

@[simp]
/--
lemma `extClass_comp` / 引理 `extClass_comp`

English:
lemma extClass_comp
  statement: hS.extClass.comp (Ext.mk₀ S.f) (add_zero 1) = 0
  proof: by
  let := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom, Ext.zero_hom,
    ShiftedHom.comp_mk₀]
  exact comp_distTriang_mor_zero₃₁ _ hS.singleTriangle_distinguished

@[simp]

中文:
引理 extClass_comp
  结论: hS.extClass.comp (Ext.mk₀ S.f) (add_zero 1) = 0
  证明: by
  let := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom, Ext.zero_hom,
    ShiftedHom.comp_mk₀]
  exact comp_distTriang_mor_zero₃₁ _ hS.singleTriangle_distinguished

@[simp]

Depends on / 依赖: Ext.comp_hom, Ext.mk, Ext.zero_hom, HasDerivedCategory, HasDerivedCategory.standard, ShiftedHom, ShiftedHom.comp_mk, comp_hom, extClass_hom, hS.singleTriangle_distinguished, singleTriangle_distinguished, standard, zero_hom
-/
lemma extClass_comp : hS.extClass.comp (Ext.mk₀ S.f) (add_zero 1) = 0 := by
  let := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom, Ext.zero_hom,
    ShiftedHom.comp_mk₀]
  exact comp_distTriang_mor_zero₃₁ _ hS.singleTriangle_distinguished

@[simp]
/--
lemma `extClass_comp_assoc` / 引理 `extClass_comp_assoc`

English:
lemma extClass_comp_assoc
  given: {Y : C} {n : Nat} (γ : Ext S.X₂ Y n) {n' : Nat} {h : 1 + n = n'}
  proof: by
  rw [← Ext.comp_assoc (a₁₂ := 1) _ _ _ (by lia) (by lia) (by lia)]; rw [extClass_comp]; rw [Ext.zero_comp]

中文:
引理 extClass_comp_assoc
  条件: {Y : C} {n : 自然数} (γ : Ext S.X₂ Y n) {n' : 自然数} {h : 1 + n = n'}
  证明: by
  rw [← Ext.comp_assoc (a₁₂ := 1) _ _ _ (by lia) (by lia) (by lia)]; rw [extClass_comp]; rw [Ext.zero_comp]

Depends on / 依赖: Ext.comp_assoc, Ext.zero_comp, comp_assoc, extClass_comp, zero_comp
-/
lemma extClass_comp_assoc {Y : C} {n : Nat} (γ : Ext S.X₂ Y n) {n' : Nat} {h : 1 + n = n'} :
    hS.extClass.comp ((Ext.mk₀ S.f).comp γ (zero_add n)) h = 0 := by
  rw [← Ext.comp_assoc (a₁₂ := 1) _ _ _ (by lia) (by lia) (by lia)]; rw [extClass_comp]; rw [Ext.zero_comp]

/--
lemma `extClass_naturality` / 引理 `extClass_naturality`

English:
lemma extClass_naturality
  statement: {S₁ S₂ : ShortComplex C}
  proof: by
  let := HasDerivedCategory.standard C
  ext
  simpa [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] using! (singleTriangle.map h₁ h₂ f).comm₃

中文:
引理 extClass_naturality
  结论: {S₁ S₂ : 短复形 C}
  证明: by
  let := HasDerivedCategory.standard C
  ext
  simpa [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] using! (singleTriangle.map h₁ h₂ f).comm₃

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, ShiftedHom, ShiftedHom.comp_mk, ShiftedHom.mk, singleTriangle, singleTriangle.map, standard
-/
lemma extClass_naturality {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) :
    h₁.extClass.comp (Ext.mk₀ f.τ₁) (add_zero 1) =
      (Ext.mk₀ f.τ₃).comp h₂.extClass (zero_add 1) := by
  let := HasDerivedCategory.standard C
  ext
  simpa [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] using! (singleTriangle.map h₁ h₂ f).comm₃

end ShortExact

end ShortComplex

end CategoryTheory
