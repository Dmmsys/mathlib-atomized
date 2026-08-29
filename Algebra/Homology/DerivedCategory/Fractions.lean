/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Calculus of fractions in the derived category

We obtain various consequences of the calculus of left and right fractions
for `HomotopyCategory.quasiIso C (ComplexShape.up ℤ)` as lemmas about
factorizations of morphisms `f : Q.obj X ⟶ Q.obj Y` (where `X` and `Y`
are cochain complexes). These `f` can be factored as
a right fraction `inv (Q.map s) ≫ Q.map g` or as a left fraction
`Q.map g ≫ inv (Q.map s)`, with `s` a quasi-isomorphism (to `X` or from `Y`).
When strict bounds are known on `X` or `Y`, certain bounds may also be ensured
on the auxiliary object appearing in the fraction.

-/

public section

universe w v u

open CategoryTheory Category Limits

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (HomotopyCategory.quasiIso C (ComplexShape.up Int)).HasLeftCalculusOfFractions
  body: by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

中文:
实例 :
  签名: (HomotopyCategory.quasiIso C (ComplexShape.up 整数)).HasLeftCalculusOfFractions
  定义体: by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, infer_instance, quasiIso_eq_trW_subcategoryAcyclic
-/
instance : (HomotopyCategory.quasiIso C (ComplexShape.up Int)).HasLeftCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (HomotopyCategory.quasiIso C (ComplexShape.up Int)).HasRightCalculusOfFractions
  body: by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

中文:
实例 :
  签名: (HomotopyCategory.quasiIso C (ComplexShape.up 整数)).HasRightCalculusOfFractions
  定义体: by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, infer_instance, quasiIso_eq_trW_subcategoryAcyclic
-/
instance : (HomotopyCategory.quasiIso C (ComplexShape.up Int)).HasRightCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `right_fac` / 引理 `right_fac`

English:
lemma right_fac
  given: {X Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y)
  proof: by
  have ⟨φ, hφ⟩ := Localization.exists_rightFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', s, hs, g, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCa

中文:
引理 right_fac
  条件: {X Y : CochainComplex C 整数} (f : Q.obj X ⟶ Q.obj Y)
  证明: by
  have ⟨φ, hφ⟩ := Localization.exists_rightFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', s, hs, g, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCa

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quasiIso, HomotopyCategory.quotient, HomotopyCategory.quotient_obj_surjective, Localization, Localization.exists_rightFraction, exists_rightFraction, isIso_Qh_map_iff, map_surjective, quasiIso, quotient, quotient_obj_surjective
-/
lemma right_fac {X Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y) :
    exists (X' : CochainComplex C Int) (s : X' ⟶ X) (_ : IsIso (Q.map s)) (g : X' ⟶ Y),
      f = inv (Q.map s) ≫ Q.map g := by
  have ⟨φ, hφ⟩ := Localization.exists_rightFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', s, hs, g, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  rw [← isIso_Qh_map_iff] at hs
  exact ⟨X', s, hs, g, hφ⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `left_fac` / 引理 `left_fac`

English:
lemma left_fac
  given: {X Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y)
  proof: by
  have ⟨φ, hφ⟩ := Localization.exists_leftFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', g, s, hs, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCat

中文:
引理 left_fac
  条件: {X Y : CochainComplex C 整数} (f : Q.obj X ⟶ Q.obj Y)
  证明: by
  have ⟨φ, hφ⟩ := Localization.exists_leftFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', g, s, hs, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCat

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quasiIso, HomotopyCategory.quotient, HomotopyCategory.quotient_obj_surjective, Localization, Localization.exists_leftFraction, exists_leftFraction, isIso_Qh_map_iff, map_surjective, quasiIso, quotient, quotient_obj_surjective
-/
lemma left_fac {X Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y) :
    exists (Y' : CochainComplex C Int) (g : X ⟶ Y') (s : Y ⟶ Y') (_ : IsIso (Q.map s)),
      f = Q.map g ≫ inv (Q.map s) := by
  have ⟨φ, hφ⟩ := Localization.exists_leftFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', g, s, hs, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  rw [← isIso_Qh_map_iff] at hs
  exact ⟨X', g, s, hs, hφ⟩

/--
lemma `right_fac_of_isStrictlyLE` / 引理 `right_fac_of_isStrictlyLE`

English:
lemma right_fac_of_isStrictlyLE
  statement: {X Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y) (n : Int)
  proof: by
  obtain ⟨X', s, hs, g, rfl⟩ := right_fac f
  have : IsIso (Q.map (CochainComplex.truncLEMap s n)) := by
    rw [isIso_Q_map_iff_quasiIso]; rw [CochainComplex.quasiIso_truncLEMap_iff]
    rw [isIso_Q_map_iff_quasiIso] at hs
    infer_instance
  refine ⟨X'.truncLE n, inferInstance, CochainComplex.

中文:
引理 right_fac_of_isStrictlyLE
  结论: {X Y : CochainComplex C 整数} (f : Q.obj X ⟶ Q.obj Y) (n : 整数)
  证明: by
  obtain ⟨X', s, hs, g, rfl⟩ := right_fac f
  have : IsIso (Q.map (CochainComplex.truncLEMap s n)) := by
    rw [isIso_Q_map_iff_quasiIso]; rw [CochainComplex.quasiIso_truncLEMap_iff]
    rw [isIso_Q_map_iff_quasiIso] at hs
    infer_instance
  refine ⟨X'.truncLE n, inferInstance, CochainComplex.

Depends on / 依赖: CochainComplex, CochainComplex.quasiIso_truncLEMap_iff, CochainComplex.truncLEMap, Q.map, Q.map_comp, infer_instance, isIso_Q_map_iff_quasiIso, map_comp, quasiIso_truncLEMap_iff, right_fac, truncLE, truncLEMap
-/
lemma right_fac_of_isStrictlyLE {X Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y) (n : Int)
    [X.IsStrictlyLE n] :
    exists (X' : CochainComplex C Int) (_ : X'.IsStrictlyLE n) (s : X' ⟶ X) (_ : IsIso (Q.map s))
      (g : X' ⟶ Y), f = inv (Q.map s) ≫ Q.map g := by
  obtain ⟨X', s, hs, g, rfl⟩ := right_fac f
  have : IsIso (Q.map (CochainComplex.truncLEMap s n)) := by
    rw [isIso_Q_map_iff_quasiIso]; rw [CochainComplex.quasiIso_truncLEMap_iff]
    rw [isIso_Q_map_iff_quasiIso] at hs
    infer_instance
  refine ⟨X'.truncLE n, inferInstance, CochainComplex.truncLEMap s n ≫ X.ιTruncLE n, ?_,
      CochainComplex.truncLEMap g n ≫ Y.ιTruncLE n, ?_⟩
  · rw [Q.map_comp]
    infer_instance
  · simp

/--
lemma `left_fac_of_isStrictlyGE` / 引理 `left_fac_of_isStrictlyGE`

English:
lemma left_fac_of_isStrictlyGE
  statement: {X Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y) (n : Int)
  proof: by
  obtain ⟨Y', g, s, hs, rfl⟩ := left_fac f
  have : IsIso (Q.map (CochainComplex.truncGEMap s n)) := by
    rw [isIso_Q_map_iff_quasiIso]; rw [CochainComplex.quasiIso_truncGEMap_iff]
    rw [isIso_Q_map_iff_quasiIso] at hs
    infer_instance
  refine ⟨Y'.truncGE n, inferInstance, X.πTruncGE n ≫ C

中文:
引理 left_fac_of_isStrictlyGE
  结论: {X Y : CochainComplex C 整数} (f : Q.obj X ⟶ Q.obj Y) (n : 整数)
  证明: by
  obtain ⟨Y', g, s, hs, rfl⟩ := left_fac f
  have : IsIso (Q.map (CochainComplex.truncGEMap s n)) := by
    rw [isIso_Q_map_iff_quasiIso]; rw [CochainComplex.quasiIso_truncGEMap_iff]
    rw [isIso_Q_map_iff_quasiIso] at hs
    infer_instance
  refine ⟨Y'.truncGE n, inferInstance, X.πTruncGE n ≫ C

Depends on / 依赖: CochainCom, CochainComplex, CochainComplex.quasiIso_truncGEMap_iff, CochainComplex.truncGEMap, Q.congr_map, Q.map, Q.map_comp, congr_map, infer_instance, isIso_Q_map_iff_quasiIso, left_fac, map_comp, quasiIso_truncGEMap_iff, truncGE, truncGEMap
-/
lemma left_fac_of_isStrictlyGE {X Y : CochainComplex C Int} (f : Q.obj X ⟶ Q.obj Y) (n : Int)
    [Y.IsStrictlyGE n] :
    exists (Y' : CochainComplex C Int) (_ : Y'.IsStrictlyGE n) (g : X ⟶ Y') (s : Y ⟶ Y')
      (_ : IsIso (Q.map s)), f = Q.map g ≫ inv (Q.map s) := by
  obtain ⟨Y', g, s, hs, rfl⟩ := left_fac f
  have : IsIso (Q.map (CochainComplex.truncGEMap s n)) := by
    rw [isIso_Q_map_iff_quasiIso]; rw [CochainComplex.quasiIso_truncGEMap_iff]
    rw [isIso_Q_map_iff_quasiIso] at hs
    infer_instance
  refine ⟨Y'.truncGE n, inferInstance, X.πTruncGE n ≫ CochainComplex.truncGEMap g n,
    Y.πTruncGE n ≫ CochainComplex.truncGEMap s n, ?_, ?_⟩
  · rw [Q.map_comp]
    infer_instance
  · have eq := Q.congr_map (CochainComplex.πTruncGE_naturality s n)
    have eq' := Q.congr_map (CochainComplex.πTruncGE_naturality g n)
    simp only [Functor.map_comp] at eq eq'
    simp only [Functor.map_comp, ← cancel_mono (Q.map (CochainComplex.πTruncGE Y n)
      ≫ Q.map (CochainComplex.truncGEMap s n)), assoc, IsIso.inv_hom_id, comp_id]
    simp only [eq, IsIso.inv_hom_id_assoc, eq']

/--
lemma `right_fac_of_isStrictlyLE_of_isStrictlyGE` / 引理 `right_fac_of_isStrictlyLE_of_isStrictlyGE`

English:
lemma right_fac_of_isStrictlyLE_of_isStrictlyGE
  proof: by
  obtain ⟨X', hX', s, hs, g, fac⟩ := right_fac_of_isStrictlyLE f b
  have : IsIso (Q.map (CochainComplex.truncGEMap s a)) := by
    rw [isIso_Q_map_iff_quasiIso] at hs
    rw [isIso_Q_map_iff_quasiIso]; rw [CochainComplex.quasiIso_truncGEMap_iff]
    infer_instance
  refine ⟨X'.truncGE a, inferIn

中文:
引理 right_fac_of_isStrictlyLE_of_isStrictlyGE
  证明: by
  obtain ⟨X', hX', s, hs, g, fac⟩ := right_fac_of_isStrictlyLE f b
  have : IsIso (Q.map (CochainComplex.truncGEMap s a)) := by
    rw [isIso_Q_map_iff_quasiIso] at hs
    rw [isIso_Q_map_iff_quasiIso]; rw [CochainComplex.quasiIso_truncGEMap_iff]
    infer_instance
  refine ⟨X'.truncGE a, inferIn

Depends on / 依赖: CochainComplex, CochainComplex.quasiIso_truncGEMap_iff, CochainComplex.truncGEMap, Functor, Functor.map_comp, Functor.map_inv, Q.map, Q.map_comp, infer_instance, isIso_Q_map_iff_quasiIso, map_comp, map_inv, quasiIso_truncGEMap_iff, right_fac_of_isStrictlyLE, truncGE, truncGEMap
-/
lemma right_fac_of_isStrictlyLE_of_isStrictlyGE
    {X Y : CochainComplex C Int} (a b : Int) [X.IsStrictlyGE a] [X.IsStrictlyLE b]
    [Y.IsStrictlyGE a] (f : Q.obj X ⟶ Q.obj Y) :
    exists (X' : CochainComplex C Int) (_ : X'.IsStrictlyGE a) (_ : X'.IsStrictlyLE b)
    (s : X' ⟶ X) (_ : IsIso (Q.map s)) (g : X' ⟶ Y), f = inv (Q.map s) ≫ Q.map g := by
  obtain ⟨X', hX', s, hs, g, fac⟩ := right_fac_of_isStrictlyLE f b
  have : IsIso (Q.map (CochainComplex.truncGEMap s a)) := by
    rw [isIso_Q_map_iff_quasiIso] at hs
    rw [isIso_Q_map_iff_quasiIso]; rw [CochainComplex.quasiIso_truncGEMap_iff]
    infer_instance
  refine ⟨X'.truncGE a, inferInstance, inferInstance,
    CochainComplex.truncGEMap s a ≫ inv (X.πTruncGE a), ?_,
      CochainComplex.truncGEMap g a ≫ inv (Y.πTruncGE a), ?_⟩
  · rw [Q.map_comp]
    infer_instance
  · simp only [Functor.map_comp, Functor.map_inv, IsIso.inv_comp, IsIso.inv_inv, assoc, fac,
      ← cancel_epi (Q.map s), IsIso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc]; rw [← CochainComplex.πTruncGE_naturality s a]; rw [Functor.map_comp]; rw [assoc]; rw [IsIso.hom_inv_id_assoc]; rw [← Functor.map_comp_assoc]; rw [CochainComplex.πTruncGE_naturality g a]; rw [Functor.map_comp]; rw [assoc]; rw [IsIso.hom_inv_id]; rw [comp_id]

/--
lemma `left_fac_of_isStrictlyLE_of_isStrictlyGE` / 引理 `left_fac_of_isStrictlyLE_of_isStrictlyGE`

English:
lemma left_fac_of_isStrictlyLE_of_isStrictlyGE
  proof: by
  obtain ⟨Y', hY', g, s, hs, fac⟩ := left_fac_of_isStrictlyGE f a
  have : IsIso (Q.map (CochainComplex.truncLEMap s b)) := by
    rw [isIso_Q_map_iff_quasiIso] at hs
    rw [isIso_Q_map_iff_quasiIso]; rw [CochainComplex.quasiIso_truncLEMap_iff]
    infer_instance
  refine ⟨Y'.truncLE b, inferIns

中文:
引理 left_fac_of_isStrictlyLE_of_isStrictlyGE
  证明: by
  obtain ⟨Y', hY', g, s, hs, fac⟩ := left_fac_of_isStrictlyGE f a
  have : IsIso (Q.map (CochainComplex.truncLEMap s b)) := by
    rw [isIso_Q_map_iff_quasiIso] at hs
    rw [isIso_Q_map_iff_quasiIso]; rw [CochainComplex.quasiIso_truncLEMap_iff]
    infer_instance
  refine ⟨Y'.truncLE b, inferIns

Depends on / 依赖: CochainComplex, CochainComplex.quasiIso_truncLEMap_iff, CochainComplex.truncLEMap, Functor, Functor.map_comp, Functor.map_inv, Q.map, Q.map_comp, infer_instance, isIso_Q_map_iff_quasiIso, left_fac_of_isStrictlyGE, map_comp, map_inv, quasiIso_truncLEMap_iff, truncLE, truncLEMap
-/
lemma left_fac_of_isStrictlyLE_of_isStrictlyGE
    {X Y : CochainComplex C Int} (a b : Int)
    [X.IsStrictlyLE b] [Y.IsStrictlyGE a] [Y.IsStrictlyLE b] (f : Q.obj X ⟶ Q.obj Y) :
    exists (Y' : CochainComplex C Int) (_ : Y'.IsStrictlyGE a) (_ : Y'.IsStrictlyLE b)
    (g : X ⟶ Y') (s : Y ⟶ Y') (_ : IsIso (Q.map s)), f = Q.map g ≫ inv (Q.map s) := by
  obtain ⟨Y', hY', g, s, hs, fac⟩ := left_fac_of_isStrictlyGE f a
  have : IsIso (Q.map (CochainComplex.truncLEMap s b)) := by
    rw [isIso_Q_map_iff_quasiIso] at hs
    rw [isIso_Q_map_iff_quasiIso]; rw [CochainComplex.quasiIso_truncLEMap_iff]
    infer_instance
  refine ⟨Y'.truncLE b, inferInstance, inferInstance,
    inv (X.ιTruncLE b) ≫ CochainComplex.truncLEMap g b,
    inv (Y.ιTruncLE b) ≫ CochainComplex.truncLEMap s b, ?_, ?_⟩
  · rw [Q.map_comp]
    infer_instance
  · simp only [Functor.map_comp, Functor.map_inv, IsIso.inv_comp, IsIso.inv_inv, assoc, fac,
      ← cancel_mono (Q.map s), IsIso.inv_hom_id, comp_id]
    rw [← Functor.map_comp]; rw [← CochainComplex.ιTruncLE_naturality s b]; rw [Functor.map_comp]; rw [IsIso.inv_hom_id_assoc]; rw [← Functor.map_comp]; rw [CochainComplex.ιTruncLE_naturality g b]; rw [Functor.map_comp]; rw [IsIso.inv_hom_id_assoc]

/--
lemma `subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE` / 引理 `subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE`

English:
lemma subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE
  statement: (X Y : CochainComplex C Int)
  proof: by
  suffices forall (f : Q.obj X ⟶ Q.obj Y), f = 0 from ⟨by simp [this]⟩
  intro f
  obtain ⟨X', _, s, _, g, rfl⟩ := right_fac_of_isStrictlyLE f a
  have : g = 0 := by
    ext i
    by_cases hi : a < i
    · apply (X'.isZero_of_isStrictlyLE a i hi).eq_of_src
    · apply (Y.isZero_of_isStrictlyGE b 

中文:
引理 subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE
  结论: (X Y : CochainComplex C 整数)
  证明: by
  suffices forall (f : Q.obj X ⟶ Q.obj Y), f = 0 from ⟨by simp [this]⟩
  intro f
  obtain ⟨X', _, s, _, g, rfl⟩ := right_fac_of_isStrictlyLE f a
  have : g = 0 := by
    ext i
    by_cases hi : a < i
    · apply (X'.isZero_of_isStrictlyLE a i hi).eq_of_src
    · apply (Y.isZero_of_isStrictlyGE b 

Depends on / 依赖: Q.map_zero, Q.obj, Y.isZero_of_isStrictlyGE, comp_zero, eq_of_src, eq_of_tgt, isZero_of_isStrictlyGE, isZero_of_isStrictlyLE, map_zero, right_fac_of_isStrictlyLE
-/
lemma subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE (X Y : CochainComplex C Int)
    (a b : Int) (h : a < b) [X.IsStrictlyLE a] [Y.IsStrictlyGE b] :
    Subsingleton (Q.obj X ⟶ Q.obj Y) := by
  suffices forall (f : Q.obj X ⟶ Q.obj Y), f = 0 from ⟨by simp [this]⟩
  intro f
  obtain ⟨X', _, s, _, g, rfl⟩ := right_fac_of_isStrictlyLE f a
  have : g = 0 := by
    ext i
    by_cases hi : a < i
    · apply (X'.isZero_of_isStrictlyLE a i hi).eq_of_src
    · apply (Y.isZero_of_isStrictlyGE b i (by lia)).eq_of_tgt
  rw [this]; rw [Q.map_zero]; rw [comp_zero]

end DerivedCategory
