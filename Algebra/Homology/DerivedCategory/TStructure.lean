/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

/-!
# The canonical t-structure on the derived category

In this file, we introduce the canonical t-structure on the
derived category of an abelian category.

-/

@[expose] public section

open CategoryTheory Category Pretriangulated Triangulated Limits Preadditive

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `TStructure.t` / `TStructure.t` 的定义

English:
definition TStructure.t
  signature: : TStructure (DerivedCategory C) where
  body: exists (K : CochainComplex C Int) (_ : X ≅ DerivedCategory.Q.obj K), K.IsStrictlyLE n
  ge n X := exists (K : CochainComplex C Int) (_ : X ≅ DerivedCategory.Q.obj K), K.IsStrictlyGE n
  le_isClosedUnderIsomorphisms n :=
    { of_iso := by
        rintro X Y e ⟨K, e', _⟩
        exact ⟨K, e.symm ≪≫ e

中文:
定义 TStructure.t
  签名: : TStructure (导出范畴 C) where
  定义体: exists (K : CochainComplex C Int) (_ : X ≅ DerivedCategory.Q.obj K), K.IsStrictlyLE n
  ge n X := exists (K : CochainComplex C Int) (_ : X ≅ DerivedCategory.Q.obj K), K.IsStrictlyGE n
  le_isClosedUnderIsomorphisms n :=
    { of_iso := by
        rintro X Y e ⟨K, e', _⟩
        exact ⟨K, e.symm ≪≫ e
-/
noncomputable def TStructure.t : TStructure (DerivedCategory C) where
  le n X := exists (K : CochainComplex C Int) (_ : X ≅ DerivedCategory.Q.obj K), K.IsStrictlyLE n
  ge n X := exists (K : CochainComplex C Int) (_ : X ≅ DerivedCategory.Q.obj K), K.IsStrictlyGE n
  le_isClosedUnderIsomorphisms n :=
    { of_iso := by
        rintro X Y e ⟨K, e', _⟩
        exact ⟨K, e.symm ≪≫ e', inferInstance⟩ }
  ge_isClosedUnderIsomorphisms n :=
    { of_iso := by
        rintro X Y e ⟨K, e', _⟩
        exact ⟨K, e.symm ≪≫ e', inferInstance⟩ }
  le_shift := by
    rintro n a n' h X ⟨K, e, _⟩
    exact ⟨(shiftFunctor (CochainComplex C Int) a).obj K,
      (shiftFunctor (DerivedCategory C) a).mapIso e ≪≫ (Q.commShiftIso a).symm.app K,
      K.isStrictlyLE_shift n a n' h⟩
  ge_shift := by
    rintro n a n' h X ⟨K, e, _⟩
    exact ⟨(shiftFunctor (CochainComplex C Int) a).obj K,
      (shiftFunctor (DerivedCategory C) a).mapIso e ≪≫ (Q.commShiftIso a).symm.app K,
      K.isStrictlyGE_shift n a n' h⟩
  zero' X Y f := by
    rintro ⟨K, e₁, _⟩ ⟨L, e₂, _⟩
    rw [← cancel_epi e₁.inv]; rw [← cancel_mono e₂.hom]; rw [comp_zero]; rw [zero_comp]
    apply (subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE K L 0 1 (by simp)).elim
  le_zero_le := by
    rintro X ⟨K, e, _⟩
    exact ⟨K, e, K.isStrictlyLE_of_le 0 1 (by lia)⟩
  ge_one_le := by
    rintro X ⟨K, e, _⟩
    exact ⟨K, e, K.isStrictlyGE_of_ge 0 1 (by lia)⟩
  exists_triangle_zero_one X := by
    obtain ⟨K, ⟨e₂⟩⟩ : exists K, Nonempty (Q.obj K ≅ X) := ⟨_, ⟨Q.objObjPreimageIso X⟩⟩
    have h := K.shortComplexTruncLE_shortExact 0
    refine ⟨Q.obj (K.truncLE 0), Q.obj (K.truncGE 1),
      ⟨_, Iso.refl _, inferInstance⟩, ⟨_, Iso.refl _, inferInstance⟩,
      Q.map (K.ιTruncLE 0) ≫ e₂.hom, e₂.inv ≫ Q.map (K.πTruncGE 1),
      inv (Q.map (K.shortComplexTruncLEX₃ToTruncGE 0 1 (by lia))) ≫ (triangleOfSES h).mor₃,
      isomorphic_distinguished _ (triangleOfSES_distinguished h) _ (Iso.symm ?_)⟩
    refine Triangle.isoMk _ _ (Iso.refl _) e₂
      (asIso (Q.map (K.shortComplexTruncLEX₃ToTruncGE 0 1 (by lia)))) ?_ ?_ (by simp)
    · dsimp
      rw [id_comp]
      rfl
    · dsimp
      rw [← Q.map_comp]; rw [CochainComplex.g_shortComplexTruncLEX₃ToTruncGE ..]; rw [Iso.hom_inv_id_assoc]

/--
Definition of `IsLE` / `IsLE` 的定义

English:
abbreviation IsLE
  signature: (X : DerivedCategory C) (n : Int)
  body: TStructure.t.IsLE X n

中文:
缩写 是LE
  签名: (X : 导出范畴 C) (n : 整数)
  定义体: TStructure.t.IsLE X n

Depends on / 依赖: TStructure, TStructure.t.IsLE
-/
abbrev IsLE (X : DerivedCategory C) (n : Int) : Prop := TStructure.t.IsLE X n

/--
Definition of `IsGE` / `IsGE` 的定义

English:
abbreviation IsGE
  signature: (X : DerivedCategory C) (n : Int)
  body: TStructure.t.IsGE X n

中文:
缩写 是GE
  签名: (X : 导出范畴 C) (n : 整数)
  定义体: TStructure.t.IsGE X n

Depends on / 依赖: TStructure, TStructure.t.IsGE
-/
abbrev IsGE (X : DerivedCategory C) (n : Int) : Prop := TStructure.t.IsGE X n

/--
lemma `isGE_iff` / 引理 `isGE_iff`

English:
lemma isGE_iff
  given: (X : DerivedCategory C) (n : Int)
  proof: by
  constructor
  · rintro ⟨K, e, _⟩ i hi
    apply ((K.exactAt_of_isGE n i hi).isZero_homology).of_iso
    exact (homologyFunctor C i).mapIso e ≪≫ (homologyFunctorFactors C i).app K
  · intro hX
    have : (Q.objPreimage X).IsGE n := by
      rw [CochainComplex.isGE_iff]
      intro i hi
      rw 

中文:
引理 isGE_iff
  条件: (X : 导出范畴 C) (n : 整数)
  证明: by
  constructor
  · rintro ⟨K, e, _⟩ i hi
    apply ((K.exactAt_of_isGE n i hi).isZero_homology).of_iso
    exact (homologyFunctor C i).mapIso e ≪≫ (homologyFunctorFactors C i).app K
  · intro hX
    have : (Q.objPreimage X).IsGE n := by
      rw [CochainComplex.isGE_iff]
      intro i hi
      rw 

Depends on / 依赖: CochainComplex, CochainComplex.isGE_iff, HomologicalComplex, HomologicalComplex.exactAt_iff_isZero_homology, K.exactAt_of_isGE, Q.objObjPreimageIso, Q.objPreimage, exactAt_iff_isZero_homology, exactAt_of_isGE, homologyFunctor, homologyFunctorFactors, isGE_iff, isZero_homology, mapIso, objObjPreimageIso, objPreimage, of_iso, symm.app, truncGE
-/
lemma isGE_iff (X : DerivedCategory C) (n : Int) :
    X.IsGE n ↔ forall (i : Int) (_ : i < n), IsZero ((homologyFunctor C i).obj X) := by
  constructor
  · rintro ⟨K, e, _⟩ i hi
    apply ((K.exactAt_of_isGE n i hi).isZero_homology).of_iso
    exact (homologyFunctor C i).mapIso e ≪≫ (homologyFunctorFactors C i).app K
  · intro hX
    have : (Q.objPreimage X).IsGE n := by
      rw [CochainComplex.isGE_iff]
      intro i hi
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      apply (hX i hi).of_iso
      exact (homologyFunctorFactors C i).symm.app _ ≪≫
        (homologyFunctor C i).mapIso (Q.objObjPreimageIso X)
    exact ⟨(Q.objPreimage X).truncGE n, (Q.objObjPreimageIso X).symm ≪≫
      asIso (Q.map ((Q.objPreimage X).πTruncGE n)), inferInstance⟩

/--
lemma `isLE_iff` / 引理 `isLE_iff`

English:
lemma isLE_iff
  given: (X : DerivedCategory C) (n : Int)
  proof: by
  constructor
  · rintro ⟨K, e, _⟩ i hi
    apply ((K.exactAt_of_isLE n i hi).isZero_homology).of_iso
    exact (homologyFunctor C i).mapIso e ≪≫ (homologyFunctorFactors C i).app K
  · intro hX
    have : (Q.objPreimage X).IsLE n := by
      rw [CochainComplex.isLE_iff]
      intro i hi
      rw 

中文:
引理 isLE_iff
  条件: (X : 导出范畴 C) (n : 整数)
  证明: by
  constructor
  · rintro ⟨K, e, _⟩ i hi
    apply ((K.exactAt_of_isLE n i hi).isZero_homology).of_iso
    exact (homologyFunctor C i).mapIso e ≪≫ (homologyFunctorFactors C i).app K
  · intro hX
    have : (Q.objPreimage X).IsLE n := by
      rw [CochainComplex.isLE_iff]
      intro i hi
      rw 

Depends on / 依赖: CochainComplex, CochainComplex.isLE_iff, HomologicalComplex, HomologicalComplex.exactAt_iff_isZero_homology, K.exactAt_of_isLE, Q.objObjPreimageIso, Q.objPreimage, exactAt_iff_isZero_homology, exactAt_of_isLE, homologyFunctor, homologyFunctorFactors, isLE_iff, isZero_homology, mapIso, objObjPreimageIso, objPreimage, of_iso, symm.app, truncLE
-/
lemma isLE_iff (X : DerivedCategory C) (n : Int) :
    X.IsLE n ↔ forall (i : Int) (_ : n < i), IsZero ((homologyFunctor C i).obj X) := by
  constructor
  · rintro ⟨K, e, _⟩ i hi
    apply ((K.exactAt_of_isLE n i hi).isZero_homology).of_iso
    exact (homologyFunctor C i).mapIso e ≪≫ (homologyFunctorFactors C i).app K
  · intro hX
    have : (Q.objPreimage X).IsLE n := by
      rw [CochainComplex.isLE_iff]
      intro i hi
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      apply (hX i hi).of_iso
      exact (homologyFunctorFactors C i).symm.app _ ≪≫
        (homologyFunctor C i).mapIso (Q.objObjPreimageIso X)
    exact ⟨(Q.objPreimage X).truncLE n, (Q.objObjPreimageIso X).symm ≪≫
      (asIso (Q.map ((Q.objPreimage X).ιTruncLE n))).symm, inferInstance⟩

/--
lemma `isZero_of_isGE` / 引理 `isZero_of_isGE`

English:
lemma isZero_of_isGE
  given: (X : DerivedCategory C) (n i : Int) (hi : i < n) [hX : X.IsGE n]
  proof: by
  rw [isGE_iff] at hX
  exact hX i hi

中文:
引理 isZero_of_isGE
  条件: (X : 导出范畴 C) (n i : 整数) (hi : i < n) [hX : X.是GE n]
  证明: by
  rw [isGE_iff] at hX
  exact hX i hi

Depends on / 依赖: isGE_iff
-/
lemma isZero_of_isGE (X : DerivedCategory C) (n i : Int) (hi : i < n) [hX : X.IsGE n] :
    IsZero ((homologyFunctor _ i).obj X) := by
  rw [isGE_iff] at hX
  exact hX i hi

/--
lemma `isZero_of_isLE` / 引理 `isZero_of_isLE`

English:
lemma isZero_of_isLE
  given: (X : DerivedCategory C) (n i : Int) (hi : n < i) [hX : X.IsLE n]
  proof: by
  rw [isLE_iff] at hX
  exact hX i hi

中文:
引理 isZero_of_isLE
  条件: (X : 导出范畴 C) (n i : 整数) (hi : n < i) [hX : X.是LE n]
  证明: by
  rw [isLE_iff] at hX
  exact hX i hi

Depends on / 依赖: isLE_iff
-/
lemma isZero_of_isLE (X : DerivedCategory C) (n i : Int) (hi : n < i) [hX : X.IsLE n] :
    IsZero ((homologyFunctor _ i).obj X) := by
  rw [isLE_iff] at hX
  exact hX i hi

/--
lemma `isGE_Q_obj_iff` / 引理 `isGE_Q_obj_iff`

English:
lemma isGE_Q_obj_iff
  given: (K : CochainComplex C Int) (n : Int)
  proof: by
  have eq := fun i => ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [isGE_iff, CochainComplex.isGE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]

中文:
引理 isGE_Q_obj_iff
  条件: (K : 上链复形 C 整数) (n : 整数)
  证明: by
  have eq := fun i => ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [isGE_iff, CochainComplex.isGE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]

Depends on / 依赖: CochainComplex, CochainComplex.isGE_iff, Functor, Functor.comp_obj, HomologicalComplex, HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.homologyFunctor_obj, comp_obj, exactAt_iff_isZero_homology, homologyFunctorFactors, homologyFunctor_obj, isGE_iff, isZero_iff
-/
lemma isGE_Q_obj_iff (K : CochainComplex C Int) (n : Int) :
    (Q.obj K).IsGE n ↔ K.IsGE n := by
  have eq := fun i => ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [isGE_iff, CochainComplex.isGE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]

/--
lemma `isLE_Q_obj_iff` / 引理 `isLE_Q_obj_iff`

English:
lemma isLE_Q_obj_iff
  given: (K : CochainComplex C Int) (n : Int)
  proof: by
  have eq := fun i => ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [isLE_iff, CochainComplex.isLE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]

中文:
引理 isLE_Q_obj_iff
  条件: (K : 上链复形 C 整数) (n : 整数)
  证明: by
  have eq := fun i => ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [isLE_iff, CochainComplex.isLE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]

Depends on / 依赖: CochainComplex, CochainComplex.isLE_iff, Functor, Functor.comp_obj, HomologicalComplex, HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.homologyFunctor_obj, comp_obj, exactAt_iff_isZero_homology, homologyFunctorFactors, homologyFunctor_obj, isLE_iff, isZero_iff
-/
lemma isLE_Q_obj_iff (K : CochainComplex C Int) (n : Int) :
    (Q.obj K).IsLE n ↔ K.IsLE n := by
  have eq := fun i => ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [isLE_iff, CochainComplex.isLE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]

instance (K : CochainComplex C Int) (n : Int) [K.IsGE n] :
    (Q.obj K).IsGE n := by
  rw [isGE_Q_obj_iff]
  infer_instance

instance (K : CochainComplex C Int) (n : Int) [K.IsLE n] :
    (Q.obj K).IsLE n := by
  rw [isLE_Q_obj_iff]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (X : C) (n : Int) : ((singleFunctor C n).obj X).IsGE n := by
  let e := (singleFunctorIsoCompQ C n).app X
  dsimp only [Functor.comp_obj] at e
  exact TStructure.t.isGE_of_iso e.symm n

set_option backward.defeqAttrib.useBackward true in
instance (X : C) (n : Int) : ((singleFunctor C n).obj X).IsLE n := by
  let e := (singleFunctorIsoCompQ C n).app X
  dsimp only [Functor.comp_obj] at e
  exact TStructure.t.isLE_of_iso e.symm n

/--
lemma `exists_iso_Q_obj_of_isLE` / 引理 `exists_iso_Q_obj_of_isLE`

English:
lemma exists_iso_Q_obj_of_isLE
  given: (X : DerivedCategory C) (n : Int) [hX : X.IsLE n]
  proof: by
  obtain ⟨K, e, _⟩ := hX
  exact ⟨K, inferInstance, ⟨e⟩⟩

中文:
引理 存在_iso_Q_obj_of_isLE
  条件: (X : 导出范畴 C) (n : 整数) [hX : X.是LE n]
  证明: by
  obtain ⟨K, e, _⟩ := hX
  exact ⟨K, inferInstance, ⟨e⟩⟩
-/
lemma exists_iso_Q_obj_of_isLE (X : DerivedCategory C) (n : Int) [hX : X.IsLE n] :
    exists (K : CochainComplex C Int) (_ : K.IsStrictlyLE n), Nonempty (X ≅ Q.obj K) := by
  obtain ⟨K, e, _⟩ := hX
  exact ⟨K, inferInstance, ⟨e⟩⟩

/--
lemma `exists_iso_Q_obj_of_isGE` / 引理 `exists_iso_Q_obj_of_isGE`

English:
lemma exists_iso_Q_obj_of_isGE
  given: (X : DerivedCategory C) (n : Int) [hX : X.IsGE n]
  proof: by
  obtain ⟨K, e, _⟩ := hX
  exact ⟨K, inferInstance, ⟨e⟩⟩

中文:
引理 存在_iso_Q_obj_of_isGE
  条件: (X : 导出范畴 C) (n : 整数) [hX : X.是GE n]
  证明: by
  obtain ⟨K, e, _⟩ := hX
  exact ⟨K, inferInstance, ⟨e⟩⟩
-/
lemma exists_iso_Q_obj_of_isGE (X : DerivedCategory C) (n : Int) [hX : X.IsGE n] :
    exists (K : CochainComplex C Int) (_ : K.IsStrictlyGE n), Nonempty (X ≅ Q.obj K) := by
  obtain ⟨K, e, _⟩ := hX
  exact ⟨K, inferInstance, ⟨e⟩⟩

/--
lemma `exists_iso_Q_obj_of_isGE_of_isLE` / 引理 `exists_iso_Q_obj_of_isGE_of_isLE`

English:
lemma exists_iso_Q_obj_of_isGE_of_isLE
  given: (X : DerivedCategory C) (a b : Int) [X.IsGE a] [X.IsLE b]
  proof: by
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE b
  have : K.IsGE a := by
    rw [← isGE_Q_obj_iff]
    exact TStructure.t.isGE_of_iso e a
  exact ⟨K.truncGE a, inferInstance, inferInstance, ⟨e ≪≫ asIso (Q.map (K.πTruncGE a))⟩⟩

中文:
引理 存在_iso_Q_obj_of_isGE_of_isLE
  条件: (X : 导出范畴 C) (a b : 整数) [X.是GE a] [X.是LE b]
  证明: by
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE b
  have : K.IsGE a := by
    rw [← isGE_Q_obj_iff]
    exact TStructure.t.isGE_of_iso e a
  exact ⟨K.truncGE a, inferInstance, inferInstance, ⟨e ≪≫ asIso (Q.map (K.πTruncGE a))⟩⟩

Depends on / 依赖: K.IsGE, K.truncGE, Q.map, TStructure, TStructure.t.isGE_of_iso, X.exists_iso_Q_obj_of_isLE, exists_iso_Q_obj_of_isLE, isGE_Q_obj_iff, isGE_of_iso, truncGE
-/
lemma exists_iso_Q_obj_of_isGE_of_isLE (X : DerivedCategory C) (a b : Int) [X.IsGE a] [X.IsLE b] :
    exists (K : CochainComplex C Int) (_ : K.IsStrictlyGE a) (_ : K.IsStrictlyLE b),
      Nonempty (X ≅ Q.obj K) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE b
  have : K.IsGE a := by
    rw [← isGE_Q_obj_iff]
    exact TStructure.t.isGE_of_iso e a
  exact ⟨K.truncGE a, inferInstance, inferInstance, ⟨e ≪≫ asIso (Q.map (K.πTruncGE a))⟩⟩

/--
lemma `exists_iso_singleFunctor_obj_of_isGE_of_isLE` / 引理 `exists_iso_singleFunctor_obj_of_isGE_of_isLE`

English:
lemma exists_iso_singleFunctor_obj_of_isGE_of_isLE
  proof: by
  obtain ⟨K, _, _, ⟨e⟩⟩ := exists_iso_Q_obj_of_isGE_of_isLE X n n
  obtain ⟨Y, ⟨e'⟩⟩ := CochainComplex.exists_iso_single K n
  exact ⟨Y, ⟨e ≪≫ Q.mapIso e'⟩⟩

中文:
引理 存在_iso_singleFunctor_obj_of_isGE_of_isLE
  证明: by
  obtain ⟨K, _, _, ⟨e⟩⟩ := exists_iso_Q_obj_of_isGE_of_isLE X n n
  obtain ⟨Y, ⟨e'⟩⟩ := CochainComplex.exists_iso_single K n
  exact ⟨Y, ⟨e ≪≫ Q.mapIso e'⟩⟩

Depends on / 依赖: CochainComplex, CochainComplex.exists_iso_single, Q.mapIso, exists_iso_Q_obj_of_isGE_of_isLE, exists_iso_single, mapIso
-/
lemma exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (X : DerivedCategory C) (n : Int) [X.IsGE n] [X.IsLE n] :
    exists (Y : C), Nonempty (X ≅ (singleFunctor C n).obj Y) := by
  obtain ⟨K, _, _, ⟨e⟩⟩ := exists_iso_Q_obj_of_isGE_of_isLE X n n
  obtain ⟨Y, ⟨e'⟩⟩ := CochainComplex.exists_iso_single K n
  exact ⟨Y, ⟨e ≪≫ Q.mapIso e'⟩⟩

open DerivedCategory.TStructure

variable (C)

/--
Definition of `Minus` / `Minus` 的定义

English:
abbreviation Minus
  signature: : Type max u v
  body: (t : TStructure (DerivedCategory C)).minus.FullSubcategory

中文:
缩写 Minus
  签名: : 类型 最大值 u v
  定义体: (t : TStructure (DerivedCategory C)).minus.FullSubcategory

Depends on / 依赖: DerivedCategory, FullSubcategory, TStructure, minus.FullSubcategory
-/
abbrev Minus : Type max u v := (t : TStructure (DerivedCategory C)).minus.FullSubcategory

/--
Definition of `Plus` / `Plus` 的定义

English:
abbreviation Plus
  signature: : Type max u v
  body: (t : TStructure (DerivedCategory C)).plus.FullSubcategory

中文:
缩写 Plus
  签名: : 类型 最大值 u v
  定义体: (t : TStructure (DerivedCategory C)).plus.FullSubcategory

Depends on / 依赖: DerivedCategory, FullSubcategory, TStructure, plus.FullSubcategory
-/
abbrev Plus : Type max u v := (t : TStructure (DerivedCategory C)).plus.FullSubcategory

/--
Definition of `Bounded` / `Bounded` 的定义

English:
abbreviation Bounded
  signature: : Type max u v
  body: (t : TStructure (DerivedCategory C)).bounded.FullSubcategory

中文:
缩写 有界
  签名: : 类型 最大值 u v
  定义体: (t : TStructure (DerivedCategory C)).bounded.FullSubcategory

Depends on / 依赖: DerivedCategory, FullSubcategory, TStructure, bounded, bounded.FullSubcategory
-/
abbrev Bounded : Type max u v := (t : TStructure (DerivedCategory C)).bounded.FullSubcategory

variable {C}

/--
Definition of `Minus.ι` / `Minus.ι` 的定义

English:
abbreviation Minus.ι
  signature: : Minus C ⥤ DerivedCategory C
  body: t.minus.ι

中文:
缩写 Minus.ι
  签名: : Minus C ⥤ 导出范畴 C
  定义体: t.minus.ι

Depends on / 依赖: t.minus
-/
noncomputable abbrev Minus.ι : Minus C ⥤ DerivedCategory C := t.minus.ι

/--
Definition of `Plus.ι` / `Plus.ι` 的定义

English:
abbreviation Plus.ι
  signature: : Plus C ⥤ DerivedCategory C
  body: t.plus.ι

中文:
缩写 Plus.ι
  签名: : Plus C ⥤ 导出范畴 C
  定义体: t.plus.ι

Depends on / 依赖: t.plus
-/
noncomputable abbrev Plus.ι : Plus C ⥤ DerivedCategory C := t.plus.ι

/--
Definition of `Bounded.ι` / `Bounded.ι` 的定义

English:
abbreviation Bounded.ι
  signature: : Bounded C ⥤ DerivedCategory C
  body: t.bounded.ι

中文:
缩写 有界.ι
  签名: : 有界 C ⥤ 导出范畴 C
  定义体: t.bounded.ι

Depends on / 依赖: bounded, t.bounded
-/
noncomputable abbrev Bounded.ι : Bounded C ⥤ DerivedCategory C := t.bounded.ι

end DerivedCategory
