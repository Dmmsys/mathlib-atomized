/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.CategoryTheory.Abelian.Projective.Extend

/-!
# Computing `Ext` using a projective resolution

Given a projective resolution `R` of an object `X` in an abelian category `C`,
we provide an API in order to construct elements in `Ext X Y n` in terms
of the complex `R.complex` and to make computations in the `Ext`-group.

## TODO
* Functoriality in `X`: this would involve a morphism `X ⟶ X'`, projective
  resolutions `R` and `R'` of `X` and `X'`, a lift of `X ⟶ X'` as a morphism
  of cochain complexes `R.complex ⟶ R'.complex`; in this context,
  we should be able to compute the precomposition of an element
  `R.extMk f m hm hf : Ext X' Y n` by `X ⟶ X'`.

-/

@[expose] public section

universe w v u

open CategoryTheory CochainComplex HomComplex Abelian Localization

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y : C} (R : ProjectiveResolution X) {n : Nat}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: R.cochainComplex.IsKProjective
  body: isKProjective_of_projective _ 0

中文:
实例 :
  签名: R.cochainComplex.是KProjective
  定义体: isKProjective_of_projective _ 0

Depends on / 依赖: isKProjective_of_projective
-/
instance : R.cochainComplex.IsKProjective := isKProjective_of_projective _ 0

/--
Definition of `extEquivCohomologyClass` / `extEquivCohomologyClass` 的定义

English:
definition extEquivCohomologyClass
  signature: :
  body: (SmallShiftedHom.precompEquiv.{w} R.π'
    ((by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance))).trans
      CochainComplex.HomComplex.CohomologyClass.equivOfIsKProjective.{w}.symm

中文:
定义 extEquivCohomologyClass
  签名: :
  定义体: (SmallShiftedHom.precompEquiv.{w} R.π'
    ((by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance))).trans
      CochainComplex.HomComplex.CohomologyClass.equivOfIsKProjective.{w}.symm

Depends on / 依赖: CochainComplex, CochainComplex.HomComplex.CohomologyClass.equivOfIsKProjective, CohomologyClass, HomComplex, HomologicalComplex, HomologicalComplex.mem_quasiIso_iff, SmallShiftedHom, SmallShiftedHom.precompEquiv, equivOfIsKProjective, infer_instance, mem_quasiIso_iff, precompEquiv
-/
noncomputable def extEquivCohomologyClass :
    Ext X Y n ≃ CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n :=
  (SmallShiftedHom.precompEquiv.{w} R.π'
    ((by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance))).trans
      CochainComplex.HomComplex.CohomologyClass.equivOfIsKProjective.{w}.symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `extEquivCohomologyClass_symm_mk_hom` / 引理 `extEquivCohomologyClass_symm_mk_hom`

English:
lemma extEquivCohomologyClass_symm_mk_hom
  statement: [HasDerivedCategory C]
  proof: by
  change SmallShiftedHom.equiv _ _ (.comp _ (CohomologyClass.mk x).toSmallShiftedHom _) = _
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀Inv, isoOfHom, asIso_inv,
    CohomologyClass.equiv_toSmallShiftedHom_mk,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans

中文:
引理 extEquivCohomologyClass_symm_mk_hom
  结论: [HasDerivedCategory C]
  证明: by
  change SmallShiftedHom.equiv _ _ (.comp _ (CohomologyClass.mk x).toSmallShiftedHom _) = _
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀Inv, isoOfHom, asIso_inv,
    CohomologyClass.equiv_toSmallShiftedHom_mk,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans

Depends on / 依赖: Category, Category.id_comp, CohomologyClass, CohomologyClass.equiv_toSmallShiftedHom_mk, CohomologyClass.mk, DerivedCategory, DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans, NatTrans.id_app, ShiftedHom, ShiftedHom.comp_mk, SmallShiftedHom, SmallShiftedHom.equiv, SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk, asIso_inv, equiv_comp, equiv_toSmallShiftedHom_mk
-/
lemma extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C]
    (x : Cocycle R.cochainComplex ((singleFunctor C 0).obj Y) n) :
    (R.extEquivCohomologyClass.symm (.mk x)).hom =
    (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
      inv (DerivedCategory.Q.map R.π'))).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q).comp
          (.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y))
            (zero_add _)) (add_zero _) := by
  change SmallShiftedHom.equiv _ _ (.comp _ (CohomologyClass.mk x).toSmallShiftedHom _) = _
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀Inv, isoOfHom, asIso_inv,
    CohomologyClass.equiv_toSmallShiftedHom_mk,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Iso.refl_inv]
  congr
  exact (ShiftedHom.comp_mk₀_id ..).symm

@[simp]
/--
lemma `extEquivCohomologyClass_symm_add` / 引理 `extEquivCohomologyClass_symm_add`

English:
lemma extEquivCohomologyClass_symm_add
  proof: by
  have := HasDerivedCategory.standard C
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  ext
  simp [← CohomologyClass.mk_add, extEquivCohomologyClass_symm_mk_hom, ShiftedHom.map]

中文:
引理 extEquivCohomologyClass_symm_add
  证明: by
  have := HasDerivedCategory.standard C
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  ext
  simp [← CohomologyClass.mk_add, extEquivCohomologyClass_symm_mk_hom, ShiftedHom.map]

Depends on / 依赖: CohomologyClass, CohomologyClass.mk_add, HasDerivedCategory, HasDerivedCategory.standard, ShiftedHom, ShiftedHom.map, extEquivCohomologyClass_symm_mk_hom, mk_add, mk_surjective, standard, x.mk_surjective, y.mk_surjective
-/
lemma extEquivCohomologyClass_symm_add
    (x y : CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n) :
    R.extEquivCohomologyClass.symm (x + y) =
      R.extEquivCohomologyClass.symm x + R.extEquivCohomologyClass.symm y := by
  have := HasDerivedCategory.standard C
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  ext
  simp [← CohomologyClass.mk_add, extEquivCohomologyClass_symm_mk_hom, ShiftedHom.map]

/-- If `R` is a projective resolution of `X`, then `Ext X Y n` identifies
to the type of cohomology classes of degree `n` from `R.cochainComplex`
to `(singleFunctor C 0).obj Y`. -/
@[simps!]
/--
Definition of `extAddEquivCohomologyClass` / `extAddEquivCohomologyClass` 的定义

English:
definition extAddEquivCohomologyClass
  signature: :
  body: AddEquiv.symm
    { toEquiv := R.extEquivCohomologyClass.symm
      map_add' := by simp }

@[simp]

中文:
定义 extAddEquivCohomologyClass
  签名: :
  定义体: AddEquiv.symm
    { toEquiv := R.extEquivCohomologyClass.symm
      map_add' := by simp }

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.symm, R.extEquivCohomologyClass.symm, extEquivCohomologyClass, map_add, toEquiv
-/
noncomputable def extAddEquivCohomologyClass :
    Ext X Y n ≃+ CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n :=
  AddEquiv.symm
    { toEquiv := R.extEquivCohomologyClass.symm
      map_add' := by simp }

@[simp]
/--
lemma `extEquivCohomologyClass_symm_sub` / 引理 `extEquivCohomologyClass_symm_sub`

English:
lemma extEquivCohomologyClass_symm_sub
  proof: R.extAddEquivCohomologyClass.symm.map_sub _ _

@[simp]

中文:
引理 extEquivCohomologyClass_symm_sub
  证明: R.extAddEquivCohomologyClass.symm.map_sub _ _

@[simp]

Depends on / 依赖: R.extAddEquivCohomologyClass.symm.map_sub, extAddEquivCohomologyClass, map_sub
-/
lemma extEquivCohomologyClass_symm_sub
    (x y : CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n) :
    R.extEquivCohomologyClass.symm (x - y) =
      R.extEquivCohomologyClass.symm x - R.extEquivCohomologyClass.symm y :=
  R.extAddEquivCohomologyClass.symm.map_sub _ _

@[simp]
/--
lemma `extEquivCohomologyClass_symm_neg` / 引理 `extEquivCohomologyClass_symm_neg`

English:
lemma extEquivCohomologyClass_symm_neg
  proof: R.extAddEquivCohomologyClass.symm.map_neg _

@[simp]

中文:
引理 extEquivCohomologyClass_symm_neg
  证明: R.extAddEquivCohomologyClass.symm.map_neg _

@[simp]

Depends on / 依赖: R.extAddEquivCohomologyClass.symm.map_neg, extAddEquivCohomologyClass, map_neg
-/
lemma extEquivCohomologyClass_symm_neg
    (x : CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n) :
    R.extEquivCohomologyClass.symm (-x) =
      -R.extEquivCohomologyClass.symm x :=
  R.extAddEquivCohomologyClass.symm.map_neg _

@[simp]
/--
lemma `extEquivCohomologyClass_symm_zero` / 引理 `extEquivCohomologyClass_symm_zero`

English:
lemma extEquivCohomologyClass_symm_zero
  proof: R.extAddEquivCohomologyClass.symm.map_zero

@[simp]

中文:
引理 extEquivCohomologyClass_symm_zero
  证明: R.extAddEquivCohomologyClass.symm.map_zero

@[simp]
-/
lemma extEquivCohomologyClass_symm_zero :
    (R.extEquivCohomologyClass (Y := Y) (n := n)).symm 0 = 0 :=
  R.extAddEquivCohomologyClass.symm.map_zero

@[simp]
/--
lemma `extEquivCohomologyClass_add` / 引理 `extEquivCohomologyClass_add`

English:
lemma extEquivCohomologyClass_add
  given: (x y : Ext X Y n)
  proof: R.extAddEquivCohomologyClass.map_add _ _

@[simp]

中文:
引理 extEquivCohomologyClass_add
  条件: (x y : Ext X Y n)
  证明: R.extAddEquivCohomologyClass.map_add _ _

@[simp]

Depends on / 依赖: R.extAddEquivCohomologyClass.map_add, extAddEquivCohomologyClass, map_add
-/
lemma extEquivCohomologyClass_add (x y : Ext X Y n) :
    R.extEquivCohomologyClass (x + y) =
      R.extEquivCohomologyClass x + R.extEquivCohomologyClass y :=
  R.extAddEquivCohomologyClass.map_add _ _

@[simp]
/--
lemma `extEquivCohomologyClass_sub` / 引理 `extEquivCohomologyClass_sub`

English:
lemma extEquivCohomologyClass_sub
  given: (x y : Ext X Y n)
  proof: R.extAddEquivCohomologyClass.map_sub _ _

@[simp]

中文:
引理 extEquivCohomologyClass_sub
  条件: (x y : Ext X Y n)
  证明: R.extAddEquivCohomologyClass.map_sub _ _

@[simp]

Depends on / 依赖: R.extAddEquivCohomologyClass.map_sub, extAddEquivCohomologyClass, map_sub
-/
lemma extEquivCohomologyClass_sub (x y : Ext X Y n) :
    R.extEquivCohomologyClass (x - y) =
      R.extEquivCohomologyClass x - R.extEquivCohomologyClass y :=
  R.extAddEquivCohomologyClass.map_sub _ _

@[simp]
/--
lemma `extEquivCohomologyClass_neg` / 引理 `extEquivCohomologyClass_neg`

English:
lemma extEquivCohomologyClass_neg
  given: (x : Ext X Y n)
  proof: R.extAddEquivCohomologyClass.map_neg _

中文:
引理 extEquivCohomologyClass_neg
  条件: (x : Ext X Y n)
  证明: R.extAddEquivCohomologyClass.map_neg _

Depends on / 依赖: R.extAddEquivCohomologyClass.map_neg, extAddEquivCohomologyClass, map_neg
-/
lemma extEquivCohomologyClass_neg (x : Ext X Y n) :
    R.extEquivCohomologyClass (-x) =
      -R.extEquivCohomologyClass x :=
  R.extAddEquivCohomologyClass.map_neg _

variable (X n) in
@[simp]
/--
lemma `extEquivCohomologyClass_zero` / 引理 `extEquivCohomologyClass_zero`

English:
lemma extEquivCohomologyClass_zero
  proof: R.extAddEquivCohomologyClass.map_zero

中文:
引理 extEquivCohomologyClass_zero
  证明: R.extAddEquivCohomologyClass.map_zero

Depends on / 依赖: R.extAddEquivCohomologyClass.map_zero, extAddEquivCohomologyClass, map_zero
-/
lemma extEquivCohomologyClass_zero :
    R.extEquivCohomologyClass (0 : Ext X Y n) = 0 :=
  R.extAddEquivCohomologyClass.map_zero

/--
Definition of `extMk` / `extMk` 的定义

English:
definition extMk
  signature: {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
  body: R.extEquivCohomologyClass.symm
    (.mk (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp)
      (-m) (by lia) (by simpa [cochainComplex_d _ _ _ m n rfl rfl])))

@[simp]

中文:
定义 extMk
  签名: {n : 自然数} (f : R.complex.X n ⟶ Y) (m : 自然数) (hm : n + 1 = m)
  定义体: R.extEquivCohomologyClass.symm
    (.mk (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp)
      (-m) (by lia) (by simpa [cochainComplex_d _ _ _ m n rfl rfl])))

@[simp]

Depends on / 依赖: Cocycle, Cocycle.toSingleMk, R.cochainComplexXIso, R.extEquivCohomologyClass.symm, cochainComplexXIso, cochainComplex_d, extEquivCohomologyClass, toSingleMk
-/
noncomputable def extMk {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    Ext X Y n :=
  R.extEquivCohomologyClass.symm
    (.mk (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp)
      (-m) (by lia) (by simpa [cochainComplex_d _ _ _ m n rfl rfl])))

@[simp]
/--
lemma `extEquivCohomologyClass_extMk` / 引理 `extEquivCohomologyClass_extMk`

English:
lemma extEquivCohomologyClass_extMk
  statement: {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
  proof: by
  simp [extMk]

中文:
引理 extEquivCohomologyClass_extMk
  结论: {n : 自然数} (f : R.complex.X n ⟶ Y) (m : 自然数) (hm : n + 1 = m)
  证明: by
  simp [extMk]
-/
lemma extEquivCohomologyClass_extMk {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    R.extEquivCohomologyClass (R.extMk f m hm hf) =
      (.mk (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp)
        (-m) (by lia) (by simpa [cochainComplex_d _ _ _ m n rfl rfl]))) := by
  simp [extMk]

/--
lemma `add_extMk` / 引理 `add_extMk`

English:
lemma add_extMk
  statement: {n : Nat} (f g : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
  proof: by
  simp only [extMk, Preadditive.comp_add]
  rw [Cocycle.toSingleMk_add _ _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp

中文:
引理 add_extMk
  结论: {n : 自然数} (f g : R.complex.X n ⟶ Y) (m : 自然数) (hm : n + 1 = m)
  证明: by
  simp only [extMk, Preadditive.comp_add]
  rw [Cocycle.toSingleMk_add _ _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp

Depends on / 依赖: Cocycle, Cocycle.toSingleMk_add, Preadditive, Preadditive.comp_add, cochainComplex_d, comp_add, toSingleMk_add
-/
lemma add_extMk {n : Nat} (f g : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) (hg : R.complex.d m n ≫ g = 0) :
    R.extMk f m hm hf + R.extMk g m hm hg =
      R.extMk (f + g) m hm (by simp [hf, hg]) := by
  simp only [extMk, Preadditive.comp_add]
  rw [Cocycle.toSingleMk_add _ _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp

/--
lemma `sub_extMk` / 引理 `sub_extMk`

English:
lemma sub_extMk
  statement: {n : Nat} (f g : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
  proof: by
  simp only [extMk, Preadditive.comp_sub]
  rw [Cocycle.toSingleMk_sub _ _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp

中文:
引理 sub_extMk
  结论: {n : 自然数} (f g : R.complex.X n ⟶ Y) (m : 自然数) (hm : n + 1 = m)
  证明: by
  simp only [extMk, Preadditive.comp_sub]
  rw [Cocycle.toSingleMk_sub _ _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp

Depends on / 依赖: Cocycle, Cocycle.toSingleMk_sub, Preadditive, Preadditive.comp_sub, cochainComplex_d, comp_sub, toSingleMk_sub
-/
lemma sub_extMk {n : Nat} (f g : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) (hg : R.complex.d m n ≫ g = 0) :
    R.extMk f m hm hf - R.extMk g m hm hg =
      R.extMk (f - g) m hm (by simp [hf, hg]) := by
  simp only [extMk, Preadditive.comp_sub]
  rw [Cocycle.toSingleMk_sub _ _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp

/--
lemma `neg_extMk` / 引理 `neg_extMk`

English:
lemma neg_extMk
  statement: {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
  proof: by
  simp only [extMk, Preadditive.comp_neg]
  rw [Cocycle.toSingleMk_neg _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp

@[simp]

中文:
引理 neg_extMk
  结论: {n : 自然数} (f : R.complex.X n ⟶ Y) (m : 自然数) (hm : n + 1 = m)
  证明: by
  simp only [extMk, Preadditive.comp_neg]
  rw [Cocycle.toSingleMk_neg _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp

@[simp]

Depends on / 依赖: Cocycle, Cocycle.toSingleMk_neg, Preadditive, Preadditive.comp_neg, cochainComplex_d, comp_neg, toSingleMk_neg
-/
lemma neg_extMk {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    -R.extMk f m hm hf =
      R.extMk (-f) m hm (by simp [hf]) := by
  simp only [extMk, Preadditive.comp_neg]
  rw [Cocycle.toSingleMk_neg _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp

@[simp]
/--
lemma `extMk_zero` / 引理 `extMk_zero`

English:
lemma extMk_zero
  given: {n : Nat} (m : Nat) (hm : n + 1 = m)
  proof: by
  simp [extMk]

中文:
引理 extMk_zero
  条件: {n : 自然数} (m : 自然数) (hm : n + 1 = m)
  证明: by
  simp [extMk]
-/
lemma extMk_zero {n : Nat} (m : Nat) (hm : n + 1 = m) :
    R.extMk (0 : R.complex.X n ⟶ Y) m hm (by simp) = 0 := by
  simp [extMk]

/--
lemma `extMk_hom` / 引理 `extMk_hom`

English:
lemma extMk_hom
  proof: extEquivCohomologyClass_symm_mk_hom _ _

中文:
引理 extMk_hom
  证明: extEquivCohomologyClass_symm_mk_hom _ _

Depends on / 依赖: extEquivCohomologyClass_symm_mk_hom
-/
lemma extMk_hom
    [HasDerivedCategory C] {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    (R.extMk f m hm hf).hom =
    (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
      inv (DerivedCategory.Q.map R.π'))).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp) (-m)
            (by lia) (by simpa [cochainComplex_d _ _ _ _ _ rfl rfl]))) _).comp
              (.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y))
                (zero_add _)) (add_zero _) :=
  extEquivCohomologyClass_symm_mk_hom _ _

/--
lemma `extMk_eq_zero_iff` / 引理 `extMk_eq_zero_iff`

English:
lemma extMk_eq_zero_iff
  statement: (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
  proof: by
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq,
    extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero,
    CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ (-p) (by lia)]; rw [R.cochainComplex_d _ _ _ _ rfl rfl]
  refine ⟨fun ⟨g, hg⟩ => ⟨

中文:
引理 extMk_eq_zero_iff
  结论: (f : R.complex.X n ⟶ Y) (m : 自然数) (hm : n + 1 = m)
  证明: by
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq,
    extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero,
    CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ (-p) (by lia)]; rw [R.cochainComplex_d _ _ _ _ rfl rfl]
  refine ⟨fun ⟨g, hg⟩ => ⟨

Depends on / 依赖: Category, Category.assoc, Cocycle, Cocycle.toSingleMk_mem_coboundaries_iff, CohomologyClass, CohomologyClass.mk_eq_zero_iff, R.cochainComplexXIso, R.cochainComplex_d, R.extEquivCohomologyClass.apply_eq_iff_eq, apply_eq_iff_eq, cancel_epi, cochainComplexXIso, cochainComplex_d, extEquivCohomologyClass, extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero, mk_eq_zero_iff, toSingleMk_mem_coboundaries_iff
-/
lemma extMk_eq_zero_iff (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0)
    (p : Nat) (hp : p + 1 = n) :
    R.extMk f m hm hf = 0 ↔
      exists (g : R.complex.X p ⟶ Y), R.complex.d n p ≫ g = f := by
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq,
    extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero,
    CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ (-p) (by lia)]; rw [R.cochainComplex_d _ _ _ _ rfl rfl]
  refine ⟨fun ⟨g, hg⟩ => ⟨(R.cochainComplexXIso (-p) p rfl).inv ≫ g, ?_⟩,
    fun ⟨g, hg⟩ => ⟨(R.cochainComplexXIso (-p) p rfl).hom ≫ g, by simpa⟩⟩
  rw [← cancel_epi (R.cochainComplexXIso (-n) n rfl).hom]
  simpa [Category.assoc] using hg

/--
lemma `extMk_surjective` / 引理 `extMk_surjective`

English:
lemma extMk_surjective
  given: (α : Ext X Y n) (m : Nat) (hm : n + 1 = m)
  proof: by
  obtain ⟨x, rfl⟩ := R.extEquivCohomologyClass.symm.surjective α
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.toSingleMk_surjective x (-n) (by simp) (-m) (by lia)
  refine ⟨(R.cochainComplexXIso (-n) n rfl).inv ≫ f, ?_, by simp [extMk]⟩
  rw [← cancel_epi (R.cochainComple

中文:
引理 extMk_surjective
  条件: (α : Ext X Y n) (m : 自然数) (hm : n + 1 = m)
  证明: by
  obtain ⟨x, rfl⟩ := R.extEquivCohomologyClass.symm.surjective α
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.toSingleMk_surjective x (-n) (by simp) (-m) (by lia)
  refine ⟨(R.cochainComplexXIso (-n) n rfl).inv ≫ f, ?_, by simp [extMk]⟩
  rw [← cancel_epi (R.cochainComple

Depends on / 依赖: Cocycle, Cocycle.toSingleMk_surjective, R.cochainComplexXIso, R.cochainComplex_d, R.extEquivCohomologyClass.symm.surjective, cancel_epi, cochainComplexXIso, cochainComplex_d, extEquivCohomologyClass, mk_surjective, surjective, toSingleMk_surjective, x.mk_surjective
-/
lemma extMk_surjective (α : Ext X Y n) (m : Nat) (hm : n + 1 = m) :
    exists (f : R.complex.X n ⟶ Y) (hf : R.complex.d m n ≫ f = 0),
      R.extMk f m hm hf = α := by
  obtain ⟨x, rfl⟩ := R.extEquivCohomologyClass.symm.surjective α
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.toSingleMk_surjective x (-n) (by simp) (-m) (by lia)
  refine ⟨(R.cochainComplexXIso (-n) n rfl).inv ≫ f, ?_, by simp [extMk]⟩
  rw [← cancel_epi (R.cochainComplexXIso (-m) m rfl).hom]
  simpa [R.cochainComplex_d _ _ _ _ rfl rfl] using hf

/--
lemma `extMk_comp_mk₀` / 引理 `extMk_comp_mk₀`

English:
lemma extMk_comp_mk₀
  statement: {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
  proof: by
  have := HasDerivedCategory.standard C
  ext
  simp only [extMk, Ext.comp_hom, Int.cast_ofNat_Int, Ext.mk₀_hom,
    extEquivCohomologyClass_symm_mk_hom]
  simp only [← Category.assoc]
  rw [Cocycle.toSingleMk_postcomp _ _ _ _
      (by simpa [cochainComplex_d _ _ _ m n rfl rfl]) g,
    Cocycle.e

中文:
引理 extMk_comp_mk₀
  结论: {n : 自然数} (f : R.complex.X n ⟶ Y) (m : 自然数) (hm : n + 1 = m)
  证明: by
  have := HasDerivedCategory.standard C
  ext
  simp only [extMk, Ext.comp_hom, Int.cast_ofNat_Int, Ext.mk₀_hom,
    extEquivCohomologyClass_symm_mk_hom]
  simp only [← Category.assoc]
  rw [Cocycle.toSingleMk_postcomp _ _ _ _
      (by simpa [cochainComplex_d _ _ _ m n rfl rfl]) g,
    Cocycle.e

Depends on / 依赖: Category, Category.assoc, Cocycle, Cocycle.equivHomShift_symm_postcomp, Cocycle.toSingleMk_postcomp, Ext.comp_hom, Ext.mk, HasDerivedCategory, HasDerivedCategory.standard, Int.cast_ofNat_Int, ShiftedHom, ShiftedHom.comp_assoc, ShiftedHom.comp_mk, ShiftedHom.map_comp, ShiftedHom.map_mk, add_zero, cast_ofNat_Int, cochainComplex_d, comp_assoc, comp_hom
-/
lemma extMk_comp_mk₀ {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) {Y' : C} (g : Y ⟶ Y') :
    (R.extMk f m hm hf).comp (Ext.mk₀ g) (add_zero _) =
      R.extMk (f ≫ g) m hm (by simp [reassoc_of% hf]) := by
  have := HasDerivedCategory.standard C
  ext
  simp only [extMk, Ext.comp_hom, Int.cast_ofNat_Int, Ext.mk₀_hom,
    extEquivCohomologyClass_symm_mk_hom]
  simp only [← Category.assoc]
  rw [Cocycle.toSingleMk_postcomp _ _ _ _
      (by simpa [cochainComplex_d _ _ _ m n rfl rfl]) g,
    Cocycle.equivHomShift_symm_postcomp,
    ← ShiftedHom.comp_mk₀ _ 0 rfl,
    ShiftedHom.map_comp, ShiftedHom.map_mk₀,
    ShiftedHom.comp_assoc _ _ _ (add_zero _) (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ (zero_add _) (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ (zero_add _) (zero_add _) (by simp),
    ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀, ← NatTrans.naturality]
  dsimp

variable {R} in
/--
lemma `mk₀_comp_extMk` / 引理 `mk₀_comp_extMk`

English:
lemma mk₀_comp_extMk
  statement: {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
  proof: by
  have := HasDerivedCategory.standard C
  ext
  have : (R'.cochainComplexXIso (-n) n (by lia)).hom ≫ φ.hom.f n =
      φ.hom'.f (-n) ≫ (R.cochainComplexXIso (-n) n (by lia)).hom := by
    simp [φ.hom'_f _ _ rfl]
  simp only [Ext.comp_hom, extMk_hom, Ext.mk₀_hom, reassoc_of% this]
  rw [Cocycle.to

中文:
引理 mk₀_comp_extMk
  结论: {n : 自然数} (f : R.complex.X n ⟶ Y) (m : 自然数) (hm : n + 1 = m)
  证明: by
  have := HasDerivedCategory.standard C
  ext
  have : (R'.cochainComplexXIso (-n) n (by lia)).hom ≫ φ.hom.f n =
      φ.hom'.f (-n) ≫ (R.cochainComplexXIso (-n) n (by lia)).hom := by
    simp [φ.hom'_f _ _ rfl]
  simp only [Ext.comp_hom, extMk_hom, Ext.mk₀_hom, reassoc_of% this]
  rw [Cocycle.to

Depends on / 依赖: Cocycle, Cocycle.equivHomShift_symm_precomp, Cocycle.toSingleMk_precomp, Ext.comp_hom, Ext.mk, HasDerivedCategory, HasDerivedCategory.standard, R.cochainComplexXIso, R.cochainComplex_d, ShiftedHom, ShiftedHom.comp_assoc, ShiftedHom.map_comp, ShiftedHom.mk, cochainComplexXIso, cochainComplex_d, comp_assoc, comp_hom, equivHomShift_symm_precomp, extMk_hom, hom.f
-/
lemma mk₀_comp_extMk {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0)
    {X' : C} {R' : ProjectiveResolution X'} {g : X' ⟶ X} (φ : Hom R' R g) :
    (Ext.mk₀ g).comp (R.extMk f m hm hf) (zero_add _) =
      R'.extMk (φ.hom.f n ≫ f) m hm (by simp [← φ.hom.comm_assoc, hf]) := by
  have := HasDerivedCategory.standard C
  ext
  have : (R'.cochainComplexXIso (-n) n (by lia)).hom ≫ φ.hom.f n =
      φ.hom'.f (-n) ≫ (R.cochainComplexXIso (-n) n (by lia)).hom := by
    simp [φ.hom'_f _ _ rfl]
  simp only [Ext.comp_hom, extMk_hom, Ext.mk₀_hom, reassoc_of% this]
  rw [Cocycle.toSingleMk_precomp _ _ _ (by lia)
    (by simpa [R.cochainComplex_d _ _ _ _ rfl rfl]),
    Cocycle.equivHomShift_symm_precomp,
    ← ShiftedHom.mk₀_comp 0 rfl, ShiftedHom.map_comp,
    ← ShiftedHom.comp_assoc _ _ _ (zero_add _) _ (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (add_zero _) _ (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (add_zero _) _ (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (zero_add _) _ (by simp),
    ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀]
  congr 3
  simp [← Functor.map_comp_assoc, ← Functor.map_comp]

end CategoryTheory.ProjectiveResolution
