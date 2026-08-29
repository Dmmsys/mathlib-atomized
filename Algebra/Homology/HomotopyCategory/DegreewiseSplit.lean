/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Degreewise split exact sequences of cochain complexes

The main result of this file is the lemma
`HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit` which asserts
that a triangle in `HomotopyCategory C (ComplexShape.up ℤ)`
is distinguished iff it is isomorphic to the triangle attached to a
degreewise split short exact sequence of cochain complexes.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Pretriangulated Preadditive

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe v

variable {C : Type*} [Category.{v} C] [Preadditive C]

namespace CochainComplex

open HomologicalComplex HomComplex

variable (S : ShortComplex (CochainComplex C Int))
  (σ : forall n, (S.map (eval C _ n)).Splitting)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cocycleOfDegreewiseSplit` / `cocycleOfDegreewiseSplit` 的定义

English:
definition cocycleOfDegreewiseSplit
  signature: : Cocycle S.X₃ S.X₁ 1
  body: Cocycle.mk
    (Cochain.mk (fun p q _ => (σ p).s ≫ S.X₂.d p q ≫ (σ q).r)) 2 (by lia) (by
      ext p _ rfl
      have := mono_of_mono_fac (σ (p + 2)).f_r
      have r_f := fun n => (σ n).r_f
      have s_g := fun n => (σ n).s_g
      dsimp at this r_f s_g ⊢
      rw [δ_v 1 2 (by lia) _ p (p + 2) (by lia) (p + 1) (p + 1)
        (by lia) (by lia)]; rw [Cochain.mk_v]; rw [Cochain.mk_v]; rw [show Int.negOnePow 2 = 1 by rfl]; rw [one_smul]; rw [assoc]; rw [assoc]; rw [← cancel_mono (S.f.f (p + 2))]; rw [add_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [zero_comp]; rw [← S.f.comm]; rw [reassoc_of% (r_f (p + 1))]; rw [sub_comp]; rw [comp_sub]; rw [comp_sub]; rw [assoc]; rw [id_comp]; rw [d_comp_d]; rw [comp_zero]; rw [zero_sub]; rw [← S.g.comm_assoc]; rw [reassoc_of% (s_g p)]; rw [r_f (p + 2)]; rw [comp_sub]; rw [comp_sub]; rw [comp_id]; rw [comp_sub]; rw [← S.g.comm_assoc]; rw [reassoc_of% (s_g (p + 1))]; rw [d_comp_d_assoc]; rw [zero_comp]; rw [sub_zero]; rw [neg_add_cancel])

中文:
定义 cocycleOfDegreewiseSplit
  签名: : Cocycle S.X₃ S.X₁ 1
  定义体: Cocycle.mk
    (Cochain.mk (fun p q _ => (σ p).s ≫ S.X₂.d p q ≫ (σ q).r)) 2 (by lia) (by
      ext p _ rfl
      have := mono_of_mono_fac (σ (p + 2)).f_r
      have r_f := fun n => (σ n).r_f
      have s_g := fun n => (σ n).s_g
      dsimp at this r_f s_g ⊢
      rw [δ_v 1 2 (by lia) _ p (p + 2) (by lia) (p + 1) (p + 1)
        (by lia) (by lia)]; rw [Cochain.mk_v]; rw [Cochain.mk_v]; rw [show Int.negOnePow 2 = 1 by rfl]; rw [one_smul]; rw [assoc]; rw [assoc]; rw [← cancel_mono (S.f.f (p + 2))]; rw [add_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [zero_comp]; rw [← S.f.comm]; rw [reassoc_of% (r_f (p + 1))]; rw [sub_comp]; rw [comp_sub]; rw [comp_sub]; rw [assoc]; rw [id_comp]; rw [d_comp_d]; rw [comp_zero]; rw [zero_sub]; rw [← S.g.comm_assoc]; rw [reassoc_of% (s_g p)]; rw [r_f (p + 2)]; rw [comp_sub]; rw [comp_sub]; rw [comp_id]; rw [comp_sub]; rw [← S.g.comm_assoc]; rw [reassoc_of% (s_g (p + 1))]; rw [d_comp_d_assoc]; rw [zero_comp]; rw [sub_zero]; rw [neg_add_cancel])

Depends on / 依赖: Cochain, Cochain.mk, Cochain.mk_v, Cocycle, Cocycle.mk, Int.negOnePow, S.f.f, add_comp, cancel_mono, mk_v, mono_of_mono_fac, negOnePow, one_smul
-/
def cocycleOfDegreewiseSplit : Cocycle S.X₃ S.X₁ 1 :=
  Cocycle.mk
    (Cochain.mk (fun p q _ => (σ p).s ≫ S.X₂.d p q ≫ (σ q).r)) 2 (by lia) (by
      ext p _ rfl
      have := mono_of_mono_fac (σ (p + 2)).f_r
      have r_f := fun n => (σ n).r_f
      have s_g := fun n => (σ n).s_g
      dsimp at this r_f s_g ⊢
      rw [δ_v 1 2 (by lia) _ p (p + 2) (by lia) (p + 1) (p + 1)
        (by lia) (by lia)]; rw [Cochain.mk_v]; rw [Cochain.mk_v]; rw [show Int.negOnePow 2 = 1 by rfl]; rw [one_smul]; rw [assoc]; rw [assoc]; rw [← cancel_mono (S.f.f (p + 2))]; rw [add_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [zero_comp]; rw [← S.f.comm]; rw [reassoc_of% (r_f (p + 1))]; rw [sub_comp]; rw [comp_sub]; rw [comp_sub]; rw [assoc]; rw [id_comp]; rw [d_comp_d]; rw [comp_zero]; rw [zero_sub]; rw [← S.g.comm_assoc]; rw [reassoc_of% (s_g p)]; rw [r_f (p + 2)]; rw [comp_sub]; rw [comp_sub]; rw [comp_id]; rw [comp_sub]; rw [← S.g.comm_assoc]; rw [reassoc_of% (s_g (p + 1))]; rw [d_comp_d_assoc]; rw [zero_comp]; rw [sub_zero]; rw [neg_add_cancel])

/--
Definition of `homOfDegreewiseSplit` / `homOfDegreewiseSplit` 的定义

English:
definition homOfDegreewiseSplit
  signature: : S.X₃ ⟶ S.X₁⟦(1 : Int)⟧
  body: ((Cocycle.equivHom _ _).symm ((cocycleOfDegreewiseSplit S σ).rightShift 1 0 (zero_add 1)))

中文:
定义 homOfDegreewiseSplit
  签名: : S.X₃ ⟶ S.X₁⟦(1 : 整数)⟧
  定义体: ((Cocycle.equivHom _ _).symm ((cocycleOfDegreewiseSplit S σ).rightShift 1 0 (zero_add 1)))

Depends on / 依赖: Cocycle, Cocycle.equivHom, cocycleOfDegreewiseSplit, equivHom, rightShift, zero_add
-/
def homOfDegreewiseSplit : S.X₃ ⟶ S.X₁⟦(1 : Int)⟧ :=
  ((Cocycle.equivHom _ _).symm ((cocycleOfDegreewiseSplit S σ).rightShift 1 0 (zero_add 1)))

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `homOfDegreewiseSplit_f` / 引理 `homOfDegreewiseSplit_f`

English:
lemma homOfDegreewiseSplit_f
  given: (n : Int)
  proof: by
  simp [homOfDegreewiseSplit, Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl]

中文:
引理 homOfDegreewiseSplit_f
  条件: (n : 整数)
  证明: by
  simp [homOfDegreewiseSplit, Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl]

Depends on / 依赖: Cochain, Cochain.rightShift_v, homOfDegreewiseSplit, rightShift_v
-/
lemma homOfDegreewiseSplit_f (n : Int) :
    (homOfDegreewiseSplit S σ).f n =
      (cocycleOfDegreewiseSplit S σ).1.v n (n + 1) rfl := by
  simp [homOfDegreewiseSplit, Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl]

/-- The triangle in `CochainComplex C ℤ` attached to a degreewise split short exact sequence
of cochain complexes. -/
@[simps! obj₁ obj₂ obj₃ mor₁ mor₂ mor₃]
/--
Definition of `triangleOfDegreewiseSplit` / `triangleOfDegreewiseSplit` 的定义

English:
definition triangleOfDegreewiseSplit
  signature: : Triangle (CochainComplex C Int)
  body: Triangle.mk S.f S.g (homOfDegreewiseSplit S σ)

中文:
定义 triangleOfDegreewiseSplit
  签名: : Triangle (上链复形 C 整数)
  定义体: Triangle.mk S.f S.g (homOfDegreewiseSplit S σ)

Depends on / 依赖: Triangle, Triangle.mk, homOfDegreewiseSplit
-/
def triangleOfDegreewiseSplit : Triangle (CochainComplex C Int) :=
  Triangle.mk S.f S.g (homOfDegreewiseSplit S σ)

/--
Definition of `trianglehOfDegreewiseSplit` / `trianglehOfDegreewiseSplit` 的定义

English:
abbreviation trianglehOfDegreewiseSplit
  signature: :
  body: (HomotopyCategory.quotient C (ComplexShape.up Int)).mapTriangle.obj (triangleOfDegreewiseSplit S σ)

中文:
缩写 trianglehOfDegreewiseSplit
  签名: :
  定义体: (HomotopyCategory.quotient C (ComplexShape.up Int)).mapTriangle.obj (triangleOfDegreewiseSplit S σ)

Depends on / 依赖: ComplexShape, ComplexShape.up, HomotopyCategory, HomotopyCategory.quotient, mapTriangle, mapTriangle.obj, quotient, triangleOfDegreewiseSplit
-/
noncomputable abbrev trianglehOfDegreewiseSplit :
    Triangle (HomotopyCategory C (ComplexShape.up Int)) :=
  (HomotopyCategory.quotient C (ComplexShape.up Int)).mapTriangle.obj (triangleOfDegreewiseSplit S σ)

variable [HasBinaryBiproducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mappingConeHomOfDegreewiseSplitXIso` / `mappingConeHomOfDegreewiseSplitXIso` 的定义

English:
definition mappingConeHomOfDegreewiseSplitXIso
  signature: (p q : Int) (hpq : p + 1 = q)
  body: (mappingCone.fst (homOfDegreewiseSplit S σ)).1.v p q hpq ≫ (σ q).s -
    (mappingCone.snd (homOfDegreewiseSplit S σ)).v p p (add_zero p) ≫
      (Cochain.ofHom S.f).v (p + 1) q (by lia)
  inv := S.g.f q ≫ (mappingCone.inl (homOfDegreewiseSplit S σ)).v q p (by lia) -
    (σ q).r ≫ (S.X₁.XIsoOfEq hpq.symm).hom ≫
      (mappingCone.inr (homOfDegreewiseSplit S σ)).f p
  hom_inv_id := by
    subst hpq
    have s_g := (σ (p + 1)).s_g
    have f_r := (σ (p + 1)).f_r
    dsimp at s_g f_r ⊢
    -- the following list of lemmas was obtained by doing
    -- simp? [mappingCone.ext_from_iff _ (p + 1) _ rfl, reassoc_of% f_r, reassoc_of% s_g]
    -- which may require increasing maximum heart beats
    simp only [Cochain.ofHom_v, Int.reduceNeg, id_comp, comp_sub, sub_comp, assoc,
        reassoc_of% s_g, ShortComplex.Splitting.s_r_assoc, ShortComplex.map_X₃, eval_obj,
        ShortComplex.map_X₁, zero_comp, comp_zero, reassoc_of% f_r, zero_sub, sub_neg_eq_add,
        mappingCone.ext_from_iff _ (p + 1) _ rfl, comp_add, mappingCone.inl_v_fst_v_assoc,
        mappingCone.inl_v_snd_v_assoc, shiftFunctor_obj_X', sub_zero, add_zero, comp_id,
        mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc, add_eq_right, neg_eq_zero,
        true_and]
    rw [← comp_f_assoc]; rw [S.zero]; rw [zero_f]; rw [zero_comp]
  inv_hom_id := by
    subst hpq
    have h := (σ (p + 1)).id
    dsimp at h ⊢
    simp only [id_comp, Cochain.ofHom_v, comp_sub, sub_comp, assoc, mappingCone.inl_v_fst_v_assoc,
      mappingCone.inr_f_fst_v_assoc, shiftFunctor_obj_X', zero_comp, comp_zero, sub_zero,
      mappingCone.inl_v_snd_v_assoc, mappingCone.inr_f_snd_v_assoc, zero_sub, sub_neg_eq_add, ← h]
    abel

中文:
定义 mappingConeHomOfDegreewiseSplitXIso
  签名: (p q : 整数) (hpq : p + 1 = q)
  定义体: (mappingCone.fst (homOfDegreewiseSplit S σ)).1.v p q hpq ≫ (σ q).s -
    (mappingCone.snd (homOfDegreewiseSplit S σ)).v p p (add_zero p) ≫
      (Cochain.ofHom S.f).v (p + 1) q (by lia)
  inv := S.g.f q ≫ (mappingCone.inl (homOfDegreewiseSplit S σ)).v q p (by lia) -
    (σ q).r ≫ (S.X₁.XIsoOfEq hpq.symm).hom ≫
      (mappingCone.inr (homOfDegreewiseSplit S σ)).f p
  hom_inv_id := by
    subst hpq
    have s_g := (σ (p + 1)).s_g
    have f_r := (σ (p + 1)).f_r
    dsimp at s_g f_r ⊢
    -- the following list of lemmas was obtained by doing
    -- simp? [mappingCone.ext_from_iff _ (p + 1) _ rfl, reassoc_of% f_r, reassoc_of% s_g]
    -- which may require increasing maximum heart beats
    simp only [Cochain.ofHom_v, Int.reduceNeg, id_comp, comp_sub, sub_comp, assoc,
        reassoc_of% s_g, ShortComplex.Splitting.s_r_assoc, ShortComplex.map_X₃, eval_obj,
        ShortComplex.map_X₁, zero_comp, comp_zero, reassoc_of% f_r, zero_sub, sub_neg_eq_add,
        mappingCone.ext_from_iff _ (p + 1) _ rfl, comp_add, mappingCone.inl_v_fst_v_assoc,
        mappingCone.inl_v_snd_v_assoc, shiftFunctor_obj_X', sub_zero, add_zero, comp_id,
        mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc, add_eq_right, neg_eq_zero,
        true_and]
    rw [← comp_f_assoc]; rw [S.zero]; rw [zero_f]; rw [zero_comp]
  inv_hom_id := by
    subst hpq
    have h := (σ (p + 1)).id
    dsimp at h ⊢
    simp only [id_comp, Cochain.ofHom_v, comp_sub, sub_comp, assoc, mappingCone.inl_v_fst_v_assoc,
      mappingCone.inr_f_fst_v_assoc, shiftFunctor_obj_X', zero_comp, comp_zero, sub_zero,
      mappingCone.inl_v_snd_v_assoc, mappingCone.inr_f_snd_v_assoc, zero_sub, sub_neg_eq_add, ← h]
    abel

Depends on / 依赖: homOfDegreewiseSplit, mappingCone, mappingCone.fst
-/
noncomputable def mappingConeHomOfDegreewiseSplitXIso (p q : Int) (hpq : p + 1 = q) :
    (mappingCone (homOfDegreewiseSplit S σ)).X p ≅ S.X₂.X q where
  hom := (mappingCone.fst (homOfDegreewiseSplit S σ)).1.v p q hpq ≫ (σ q).s -
    (mappingCone.snd (homOfDegreewiseSplit S σ)).v p p (add_zero p) ≫
      (Cochain.ofHom S.f).v (p + 1) q (by lia)
  inv := S.g.f q ≫ (mappingCone.inl (homOfDegreewiseSplit S σ)).v q p (by lia) -
    (σ q).r ≫ (S.X₁.XIsoOfEq hpq.symm).hom ≫
      (mappingCone.inr (homOfDegreewiseSplit S σ)).f p
  hom_inv_id := by
    subst hpq
    have s_g := (σ (p + 1)).s_g
    have f_r := (σ (p + 1)).f_r
    dsimp at s_g f_r ⊢
    -- the following list of lemmas was obtained by doing
    -- simp? [mappingCone.ext_from_iff _ (p + 1) _ rfl, reassoc_of% f_r, reassoc_of% s_g]
    -- which may require increasing maximum heart beats
    simp only [Cochain.ofHom_v, Int.reduceNeg, id_comp, comp_sub, sub_comp, assoc,
        reassoc_of% s_g, ShortComplex.Splitting.s_r_assoc, ShortComplex.map_X₃, eval_obj,
        ShortComplex.map_X₁, zero_comp, comp_zero, reassoc_of% f_r, zero_sub, sub_neg_eq_add,
        mappingCone.ext_from_iff _ (p + 1) _ rfl, comp_add, mappingCone.inl_v_fst_v_assoc,
        mappingCone.inl_v_snd_v_assoc, shiftFunctor_obj_X', sub_zero, add_zero, comp_id,
        mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc, add_eq_right, neg_eq_zero,
        true_and]
    rw [← comp_f_assoc]; rw [S.zero]; rw [zero_f]; rw [zero_comp]
  inv_hom_id := by
    subst hpq
    have h := (σ (p + 1)).id
    dsimp at h ⊢
    simp only [id_comp, Cochain.ofHom_v, comp_sub, sub_comp, assoc, mappingCone.inl_v_fst_v_assoc,
      mappingCone.inr_f_fst_v_assoc, shiftFunctor_obj_X', zero_comp, comp_zero, sub_zero,
      mappingCone.inl_v_snd_v_assoc, mappingCone.inr_f_snd_v_assoc, zero_sub, sub_neg_eq_add, ← h]
    abel

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism `mappingCone (homOfDegreewiseSplit S σ) ≅ S.X₂⟦(1 : ℤ)⟧`. -/
@[simps!]
/--
Definition of `mappingConeHomOfDegreewiseSplitIso` / `mappingConeHomOfDegreewiseSplitIso` 的定义

English:
definition mappingConeHomOfDegreewiseSplitIso
  signature: :
  body: Hom.isoOfComponents (fun p => mappingConeHomOfDegreewiseSplitXIso S σ p _ rfl) (by
    rintro p _ rfl
    have r_f := (σ (p + 1 + 1)).r_f
    have s_g := (σ (p + 1)).s_g
    dsimp at r_f s_g ⊢
    simp only [mappingConeHomOfDegreewiseSplitXIso, mappingCone.ext_from_iff _ _ _ rfl,
      mappingCone.inl_v_d_assoc _ (p + 1) _ (p + 1 + 1) (by linarith) (by lia),
      cocycleOfDegreewiseSplit, r_f, Int.reduceNeg, Cochain.ofHom_v, sub_comp, assoc,
      Hom.comm, comp_sub, mappingCone.inl_v_fst_v_assoc, mappingCone.inl_v_snd_v_assoc,
      shiftFunctor_obj_X', zero_comp, sub_zero, homOfDegreewiseSplit_f,
      mappingCone.inr_f_fst_v_assoc, comp_zero, zero_sub, mappingCone.inr_f_snd_v_assoc,
      neg_neg, mappingCone.inr_f_d_assoc, shiftFunctor_obj_d',
      Int.negOnePow_one, neg_comp, sub_neg_eq_add, zero_add, and_true,
      Units.neg_smul, one_smul, comp_neg, ShortComplex.map_X₂, eval_obj, Cocycle.mk_coe,
      Cochain.mk_v]
    simp only [← S.g.comm_assoc, reassoc_of% s_g, comp_id]
    abel)

中文:
定义 mappingConeHomOfDegreewiseSplitIso
  签名: :
  定义体: Hom.isoOfComponents (fun p => mappingConeHomOfDegreewiseSplitXIso S σ p _ rfl) (by
    rintro p _ rfl
    have r_f := (σ (p + 1 + 1)).r_f
    have s_g := (σ (p + 1)).s_g
    dsimp at r_f s_g ⊢
    simp only [mappingConeHomOfDegreewiseSplitXIso, mappingCone.ext_from_iff _ _ _ rfl,
      mappingCone.inl_v_d_assoc _ (p + 1) _ (p + 1 + 1) (by linarith) (by lia),
      cocycleOfDegreewiseSplit, r_f, Int.reduceNeg, Cochain.ofHom_v, sub_comp, assoc,
      Hom.comm, comp_sub, mappingCone.inl_v_fst_v_assoc, mappingCone.inl_v_snd_v_assoc,
      shiftFunctor_obj_X', zero_comp, sub_zero, homOfDegreewiseSplit_f,
      mappingCone.inr_f_fst_v_assoc, comp_zero, zero_sub, mappingCone.inr_f_snd_v_assoc,
      neg_neg, mappingCone.inr_f_d_assoc, shiftFunctor_obj_d',
      Int.negOnePow_one, neg_comp, sub_neg_eq_add, zero_add, and_true,
      Units.neg_smul, one_smul, comp_neg, ShortComplex.map_X₂, eval_obj, Cocycle.mk_coe,
      Cochain.mk_v]
    simp only [← S.g.comm_assoc, reassoc_of% s_g, comp_id]
    abel)

Depends on / 依赖: Cochain, Cochain.ofHom_v, Hom.comm, Hom.isoOfComponents, Int.reduceNeg, cocycleOfDegreewiseSplit, comp_sub, ext_from_iff, inl_v_d_assoc, inl_v_fst_v_assoc, inl_v_snd_v_assoc, isoOfComponents, mappingCone, mappingCone.ext_from_iff, mappingCone.inl_v_d_assoc, mappingCone.inl_v_fst_v_assoc, mappingCone.inl_v_snd_v_assoc, mappingConeHomOfDegreewiseSplitXIso, ofHom_v, reduceNeg
-/
noncomputable def mappingConeHomOfDegreewiseSplitIso :
    mappingCone (homOfDegreewiseSplit S σ) ≅ S.X₂⟦(1 : Int)⟧ :=
  Hom.isoOfComponents (fun p => mappingConeHomOfDegreewiseSplitXIso S σ p _ rfl) (by
    rintro p _ rfl
    have r_f := (σ (p + 1 + 1)).r_f
    have s_g := (σ (p + 1)).s_g
    dsimp at r_f s_g ⊢
    simp only [mappingConeHomOfDegreewiseSplitXIso, mappingCone.ext_from_iff _ _ _ rfl,
      mappingCone.inl_v_d_assoc _ (p + 1) _ (p + 1 + 1) (by linarith) (by lia),
      cocycleOfDegreewiseSplit, r_f, Int.reduceNeg, Cochain.ofHom_v, sub_comp, assoc,
      Hom.comm, comp_sub, mappingCone.inl_v_fst_v_assoc, mappingCone.inl_v_snd_v_assoc,
      shiftFunctor_obj_X', zero_comp, sub_zero, homOfDegreewiseSplit_f,
      mappingCone.inr_f_fst_v_assoc, comp_zero, zero_sub, mappingCone.inr_f_snd_v_assoc,
      neg_neg, mappingCone.inr_f_d_assoc, shiftFunctor_obj_d',
      Int.negOnePow_one, neg_comp, sub_neg_eq_add, zero_add, and_true,
      Units.neg_smul, one_smul, comp_neg, ShortComplex.map_X₂, eval_obj, Cocycle.mk_coe,
      Cochain.mk_v]
    simp only [← S.g.comm_assoc, reassoc_of% s_g, comp_id]
    abel)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv` / 引理 `shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv`

English:
lemma shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv
  proof: by
  ext n
  have h := (σ (n + 1)).f_r
  dsimp at h
  dsimp [mappingConeHomOfDegreewiseSplitXIso]
  rw [id_comp]; rw [comp_sub]; rw [← comp_f_assoc]; rw [S.zero]; rw [zero_f]; rw [zero_comp]; rw [zero_sub]; rw [reassoc_of% h]

中文:
引理 shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv
  证明: by
  ext n
  have h := (σ (n + 1)).f_r
  dsimp at h
  dsimp [mappingConeHomOfDegreewiseSplitXIso]
  rw [id_comp]; rw [comp_sub]; rw [← comp_f_assoc]; rw [S.zero]; rw [zero_f]; rw [zero_comp]; rw [zero_sub]; rw [reassoc_of% h]

Depends on / 依赖: S.zero, comp_f_assoc, comp_sub, id_comp, mappingConeHomOfDegreewiseSplitXIso, reassoc_of, zero_comp, zero_f, zero_sub
-/
lemma shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv :
    S.f⟦(1 : Int)⟧' ≫ (mappingConeHomOfDegreewiseSplitIso S σ).inv = -mappingCone.inr _ := by
  ext n
  have h := (σ (n + 1)).f_r
  dsimp at h
  dsimp [mappingConeHomOfDegreewiseSplitXIso]
  rw [id_comp]; rw [comp_sub]; rw [← comp_f_assoc]; rw [S.zero]; rw [zero_f]; rw [zero_comp]; rw [zero_sub]; rw [reassoc_of% h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `mappingConeHomOfDegreewiseSplitIso_inv_comp_triangle_mor₃` / 引理 `mappingConeHomOfDegreewiseSplitIso_inv_comp_triangle_mor₃`

English:
lemma mappingConeHomOfDegreewiseSplitIso_inv_comp_triangle_mor₃
  proof: by
  ext n
  dsimp [mappingConeHomOfDegreewiseSplitXIso]
  simp only [Int.reduceNeg, id_comp, sub_comp, assoc, mappingCone.inl_v_triangle_mor₃_f,
    shiftFunctor_obj_X, shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_inv, comp_neg, comp_id,
    mappingCone.inr_f_triangle_mor₃_f, comp_zero, sub_zero]

中文:
引理 mappingConeHomOfDegreewiseSplitIso_inv_comp_triangle_mor₃
  证明: by
  ext n
  dsimp [mappingConeHomOfDegreewiseSplitXIso]
  simp only [Int.reduceNeg, id_comp, sub_comp, assoc, mappingCone.inl_v_triangle_mor₃_f,
    shiftFunctor_obj_X, shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_inv, comp_neg, comp_id,
    mappingCone.inr_f_triangle_mor₃_f, comp_zero, sub_zero]

Depends on / 依赖: Int.reduceNeg, Iso.refl_inv, XIsoOfEq_rfl, comp_id, comp_neg, comp_zero, id_comp, mappingCone, mappingCone.inl_v_triangle_mor, mappingCone.inr_f_triangle_mor, mappingConeHomOfDegreewiseSplitXIso, reduceNeg, refl_inv, shiftFunctorObjXIso, shiftFunctor_obj_X, sub_comp, sub_zero
-/
lemma mappingConeHomOfDegreewiseSplitIso_inv_comp_triangle_mor₃ :
    (mappingConeHomOfDegreewiseSplitIso S σ).inv ≫
      (mappingCone.triangle (homOfDegreewiseSplit S σ)).mor₃ = -S.g⟦(1 : Int)⟧' := by
  ext n
  dsimp [mappingConeHomOfDegreewiseSplitXIso]
  simp only [Int.reduceNeg, id_comp, sub_comp, assoc, mappingCone.inl_v_triangle_mor₃_f,
    shiftFunctor_obj_X, shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_inv, comp_neg, comp_id,
    mappingCone.inr_f_triangle_mor₃_f, comp_zero, sub_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `triangleOfDegreewiseSplitRotateRotateIso` / `triangleOfDegreewiseSplitRotateRotateIso` 的定义

English:
definition triangleOfDegreewiseSplitRotateRotateIso
  signature: :
  body: Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (mappingConeHomOfDegreewiseSplitIso S σ).symm
    (by dsimp; simp only [comp_id, id_comp])
    (by dsimp; simp only [neg_comp, shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv,
      neg_neg, id_comp])
    (by dsimp; simp only [CategoryTheory.Functor.map_id, comp_id,
      mappingConeHomOfDegreewiseSplitIso_inv_comp_triangle_mor₃])

中文:
定义 triangleOfDegreewiseSplitRotateRotateIso
  签名: :
  定义体: Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (mappingConeHomOfDegreewiseSplitIso S σ).symm
    (by dsimp; simp only [comp_id, id_comp])
    (by dsimp; simp only [neg_comp, shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv,
      neg_neg, id_comp])
    (by dsimp; simp only [CategoryTheory.Functor.map_id, comp_id,
      mappingConeHomOfDegreewiseSplitIso_inv_comp_triangle_mor₃])

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_id, Functor, Iso.refl, Triangle, Triangle.isoMk, comp_id, id_comp, map_id, mappingConeHomOfDegreewiseSplitIso, neg_comp, neg_neg, shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv
-/
noncomputable def triangleOfDegreewiseSplitRotateRotateIso :
    (triangleOfDegreewiseSplit S σ).rotate.rotate ≅
      mappingCone.triangle (homOfDegreewiseSplit S σ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (mappingConeHomOfDegreewiseSplitIso S σ).symm
    (by dsimp; simp only [comp_id, id_comp])
    (by dsimp; simp only [neg_comp, shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv,
      neg_neg, id_comp])
    (by dsimp; simp only [CategoryTheory.Functor.map_id, comp_id,
      mappingConeHomOfDegreewiseSplitIso_inv_comp_triangle_mor₃])

/--
Definition of `trianglehOfDegreewiseSplitRotateRotateIso` / `trianglehOfDegreewiseSplitRotateRotateIso` 的定义

English:
definition trianglehOfDegreewiseSplitRotateRotateIso
  signature: :
  body: (rotate _).mapIso ((HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _) ≪≫
    (HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _ ≪≫
    (HomotopyCategory.quotient _ _).mapTriangle.mapIso
      (triangleOfDegreewiseSplitRotateRotateIso S σ)

中文:
定义 trianglehOfDegreewiseSplitRotateRotateIso
  签名: :
  定义体: (rotate _).mapIso ((HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _) ≪≫
    (HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _ ≪≫
    (HomotopyCategory.quotient _ _).mapTriangle.mapIso
      (triangleOfDegreewiseSplitRotateRotateIso S σ)

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quotient, mapIso, mapTriangle, mapTriangle.mapIso, mapTriangleRotateIso, mapTriangleRotateIso.app, quotient, rotate, triangleOfDegreewiseSplitRotateRotateIso
-/
noncomputable def trianglehOfDegreewiseSplitRotateRotateIso :
    (trianglehOfDegreewiseSplit S σ).rotate.rotate ≅
      mappingCone.triangleh (homOfDegreewiseSplit S σ) :=
  (rotate _).mapIso ((HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _) ≪≫
    (HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _ ≪≫
    (HomotopyCategory.quotient _ _).mapTriangle.mapIso
      (triangleOfDegreewiseSplitRotateRotateIso S σ)

namespace mappingCone

variable {K L : CochainComplex C Int} (φ : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
/-- Given a morphism of cochain complexes `φ`, this is the short complex
given by `(triangle φ).rotate`. -/
@[simps]
/--
Definition of `triangleRotateShortComplex` / `triangleRotateShortComplex` 的定义

English:
definition triangleRotateShortComplex
  signature: : ShortComplex (CochainComplex C Int)
  body: ShortComplex.mk (triangle φ).rotate.mor₁ (triangle φ).rotate.mor₂ (by simp)

中文:
定义 triangleRotateShortComplex
  签名: : 短复形 (上链复形 C 整数)
  定义体: ShortComplex.mk (triangle φ).rotate.mor₁ (triangle φ).rotate.mor₂ (by simp)

Depends on / 依赖: ShortComplex, ShortComplex.mk, rotate, rotate.mor, triangle
-/
noncomputable def triangleRotateShortComplex : ShortComplex (CochainComplex C Int) :=
  ShortComplex.mk (triangle φ).rotate.mor₁ (triangle φ).rotate.mor₂ (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `triangleRotateShortComplex φ` is a degreewise split short exact sequence of
cochain complexes. -/
@[simps]
/--
Definition of `triangleRotateShortComplexSplitting` / `triangleRotateShortComplexSplitting` 的定义

English:
definition triangleRotateShortComplexSplitting
  signature: (n : Int)
  body: -(inl φ).v (n + 1) n (by lia)
  r := (snd φ).v n n (add_zero n)
  id := by simp [ext_from_iff φ _ _ rfl]

中文:
定义 triangleRotateShortComplexSplitting
  签名: (n : 整数)
  定义体: -(inl φ).v (n + 1) n (by lia)
  r := (snd φ).v n n (add_zero n)
  id := by simp [ext_from_iff φ _ _ rfl]
-/
noncomputable def triangleRotateShortComplexSplitting (n : Int) :
    ((triangleRotateShortComplex φ).map (eval _ _ n)).Splitting where
  s := -(inl φ).v (n + 1) n (by lia)
  r := (snd φ).v n n (add_zero n)
  id := by simp [ext_from_iff φ _ _ rfl]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `cocycleOfDegreewiseSplit_triangleRotateShortComplexSplitting_v` / 引理 `cocycleOfDegreewiseSplit_triangleRotateShortComplexSplitting_v`

English:
lemma cocycleOfDegreewiseSplit_triangleRotateShortComplexSplitting_v
  given: (p : Int)
  proof: by
  simp [cocycleOfDegreewiseSplit, d_snd_v φ p (p + 1) rfl]

中文:
引理 cocycleOfDegreewiseSplit_triangleRotateShortComplexSplitting_v
  条件: (p : 整数)
  证明: by
  simp [cocycleOfDegreewiseSplit, d_snd_v φ p (p + 1) rfl]

Depends on / 依赖: cocycleOfDegreewiseSplit, d_snd_v
-/
lemma cocycleOfDegreewiseSplit_triangleRotateShortComplexSplitting_v (p : Int) :
    (cocycleOfDegreewiseSplit _ (triangleRotateShortComplexSplitting φ)).1.v p _ rfl =
      -φ.f _ := by
  simp [cocycleOfDegreewiseSplit, d_snd_v φ p (p + 1) rfl]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `triangleRotateIsoTriangleOfDegreewiseSplit` / `triangleRotateIsoTriangleOfDegreewiseSplit` 的定义

English:
definition triangleRotateIsoTriangleOfDegreewiseSplit
  signature: :
  body: Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by ext; simp)

中文:
定义 triangleRotateIsoTriangleOfDegreewiseSplit
  签名: :
  定义体: Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by ext; simp)

Depends on / 依赖: Iso.refl, Triangle, Triangle.isoMk
-/
noncomputable def triangleRotateIsoTriangleOfDegreewiseSplit :
    (triangle φ).rotate ≅
      triangleOfDegreewiseSplit _ (triangleRotateShortComplexSplitting φ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by ext; simp)

/--
Definition of `trianglehRotateIsoTrianglehOfDegreewiseSplit` / `trianglehRotateIsoTrianglehOfDegreewiseSplit` 的定义

English:
definition trianglehRotateIsoTrianglehOfDegreewiseSplit
  signature: :
  body: (HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _ ≪≫
    (HomotopyCategory.quotient _ _).mapTriangle.mapIso
      (triangleRotateIsoTriangleOfDegreewiseSplit φ)

中文:
定义 trianglehRotateIsoTrianglehOfDegreewiseSplit
  签名: :
  定义体: (HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _ ≪≫
    (HomotopyCategory.quotient _ _).mapTriangle.mapIso
      (triangleRotateIsoTriangleOfDegreewiseSplit φ)

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quotient, mapIso, mapTriangle, mapTriangle.mapIso, mapTriangleRotateIso, mapTriangleRotateIso.app, quotient, triangleRotateIsoTriangleOfDegreewiseSplit
-/
noncomputable def trianglehRotateIsoTrianglehOfDegreewiseSplit :
    (triangleh φ).rotate ≅
      trianglehOfDegreewiseSplit _ (triangleRotateShortComplexSplitting φ) :=
  (HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _ ≪≫
    (HomotopyCategory.quotient _ _).mapTriangle.mapIso
      (triangleRotateIsoTriangleOfDegreewiseSplit φ)

end mappingCone

end CochainComplex

namespace HomotopyCategory

variable [HasZeroObject C] [HasBinaryBiproducts C]

/--
lemma `distinguished_iff_iso_trianglehOfDegreewiseSplit` / 引理 `distinguished_iff_iso_trianglehOfDegreewiseSplit`

English:
lemma distinguished_iff_iso_trianglehOfDegreewiseSplit
  proof: by
  constructor
  · intro hT
    obtain ⟨K, L, φ, ⟨e⟩⟩ := inv_rot_of_distTriang _ hT
    exact ⟨_, _, ⟨(triangleRotation _).counitIso.symm.app _ ≪≫ (rotate _).mapIso e ≪≫
      CochainComplex.mappingCone.trianglehRotateIsoTrianglehOfDegreewiseSplit φ⟩⟩
  · rintro ⟨S, σ, ⟨e⟩⟩
    rw [rotate_distinguished_triangle]; rw [rotate_distinguished_triangle]
    refine isomorphic_distinguished _ ?_ _
      ((rotate _ ⋙ rotate _).mapIso e ≪≫
        CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso S σ)
    exact ⟨_, _, _, ⟨Iso.refl _⟩⟩

中文:
引理 distinguished_iff_iso_trianglehOfDegreewiseSplit
  证明: by
  constructor
  · intro hT
    obtain ⟨K, L, φ, ⟨e⟩⟩ := inv_rot_of_distTriang _ hT
    exact ⟨_, _, ⟨(triangleRotation _).counitIso.symm.app _ ≪≫ (rotate _).mapIso e ≪≫
      CochainComplex.mappingCone.trianglehRotateIsoTrianglehOfDegreewiseSplit φ⟩⟩
  · rintro ⟨S, σ, ⟨e⟩⟩
    rw [rotate_distinguished_triangle]; rw [rotate_distinguished_triangle]
    refine isomorphic_distinguished _ ?_ _
      ((rotate _ ⋙ rotate _).mapIso e ≪≫
        CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso S σ)
    exact ⟨_, _, _, ⟨Iso.refl _⟩⟩

Depends on / 依赖: CochainComplex, CochainComplex.mappingCone.trianglehRotateIsoTrianglehOfDegreewiseSplit, CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso, Iso.refl, counitIso, counitIso.symm.app, inv_rot_of_distTriang, isomorphic_distinguished, mapIso, mappingCone, rotate, rotate_distinguished_triangle, triangleRotation, trianglehOfDegreewiseSplitRotateRotateIso, trianglehRotateIsoTrianglehOfDegreewiseSplit
-/
lemma distinguished_iff_iso_trianglehOfDegreewiseSplit
    (T : Triangle (HomotopyCategory C (ComplexShape.up Int))) :
    (T in distTriang _) ↔ exists (S : ShortComplex (CochainComplex C Int))
      (σ : forall n, (S.map (HomologicalComplex.eval C _ n)).Splitting),
      Nonempty (T ≅ CochainComplex.trianglehOfDegreewiseSplit S σ) := by
  constructor
  · intro hT
    obtain ⟨K, L, φ, ⟨e⟩⟩ := inv_rot_of_distTriang _ hT
    exact ⟨_, _, ⟨(triangleRotation _).counitIso.symm.app _ ≪≫ (rotate _).mapIso e ≪≫
      CochainComplex.mappingCone.trianglehRotateIsoTrianglehOfDegreewiseSplit φ⟩⟩
  · rintro ⟨S, σ, ⟨e⟩⟩
    rw [rotate_distinguished_triangle]; rw [rotate_distinguished_triangle]
    refine isomorphic_distinguished _ ?_ _
      ((rotate _ ⋙ rotate _).mapIso e ≪≫
        CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso S σ)
    exact ⟨_, _, _, ⟨Iso.refl _⟩⟩

end HomotopyCategory
