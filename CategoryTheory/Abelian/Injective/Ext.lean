/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
# Computing `Ext` using an injective resolution

Given an injective resolution `R` of an object `Y` in an abelian category `C`,
we provide an API in order to construct elements in `Ext X Y n` in terms
of the complex `R.cocomplex` and to make computations in the `Ext`-group.

-/

@[expose] public section

universe w v u

open CategoryTheory CochainComplex HomComplex Abelian Localization

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y : C} (R : InjectiveResolution Y) {n : Nat}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: R.cochainComplex.IsKInjective
  body: isKInjective_of_injective _ 0

中文:
实例 :
  签名: R.cochainComplex.是KInjective
  定义体: isKInjective_of_injective _ 0

Depends on / 依赖: isKInjective_of_injective
-/
instance : R.cochainComplex.IsKInjective := isKInjective_of_injective _ 0

/--
Definition of `extEquivCohomologyClass` / `extEquivCohomologyClass` 的定义

English:
definition extEquivCohomologyClass
  signature: :
  body: (SmallShiftedHom.postcompEquiv.{w} R.ι'
      (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)).trans
    CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.{w}.symm

中文:
定义 extEquivCohomologyClass
  签名: :
  定义体: (SmallShiftedHom.postcompEquiv.{w} R.ι'
      (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)).trans
    CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.{w}.symm

Depends on / 依赖: CochainComplex, CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective, CohomologyClass, HomComplex, HomologicalComplex, HomologicalComplex.mem_quasiIso_iff, SmallShiftedHom, SmallShiftedHom.postcompEquiv, equivOfIsKInjective, infer_instance, mem_quasiIso_iff, postcompEquiv
-/
noncomputable def extEquivCohomologyClass :
    Ext X Y n ≃ CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n :=
  (SmallShiftedHom.postcompEquiv.{w} R.ι'
      (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)).trans
    CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.{w}.symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `extEquivCohomologyClass_symm_mk_hom` / 引理 `extEquivCohomologyClass_symm_mk_hom`

English:
lemma extEquivCohomologyClass_symm_mk_hom
  statement: [HasDerivedCategory C]
  proof: by
  change SmallShiftedHom.equiv _ _ ((CohomologyClass.mk x).toSmallShiftedHom.comp _ _) = _
  simp only [SmallShiftedHom.equiv_comp, CohomologyClass.equiv_toSmallShiftedHom_mk,
    SmallShiftedHom.equiv_mk₀Inv, isoOfHom, asIso_inv,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.

中文:
引理 extEquivCohomologyClass_symm_mk_hom
  结论: [HasDerivedCategory C]
  证明: by
  change SmallShiftedHom.equiv _ _ ((CohomologyClass.mk x).toSmallShiftedHom.comp _ _) = _
  simp only [SmallShiftedHom.equiv_comp, CohomologyClass.equiv_toSmallShiftedHom_mk,
    SmallShiftedHom.equiv_mk₀Inv, isoOfHom, asIso_inv,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.

Depends on / 依赖: CohomologyClass, CohomologyClass.equiv_toSmallShiftedHom_mk, CohomologyClass.mk, DerivedCategory, DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans, NatTrans.id_app, ShiftedHom, ShiftedHom.mk, SmallShiftedHom, SmallShiftedHom.equiv, SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk, asIso_inv, cat_disch, equiv_comp, equiv_toSmallShiftedHom_mk, id_app
-/
lemma extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C]
    (x : Cocycle ((singleFunctor C 0).obj X) R.cochainComplex n) :
    (R.extEquivCohomologyClass.symm (.mk x)).hom =
      (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X)).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q).comp
        (.mk₀ _ rfl (inv (DerivedCategory.Q.map R.ι') ≫
          (DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y)) (zero_add _)) (add_zero _) := by
  change SmallShiftedHom.equiv _ _ ((CohomologyClass.mk x).toSmallShiftedHom.comp _ _) = _
  simp only [SmallShiftedHom.equiv_comp, CohomologyClass.equiv_toSmallShiftedHom_mk,
    SmallShiftedHom.equiv_mk₀Inv, isoOfHom, asIso_inv,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app, Iso.refl_inv,
    ShiftedHom.mk₀_id_comp]
  congr
  cat_disch

set_option backward.defeqAttrib.useBackward true in
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
    (x y : CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n) :
    R.extEquivCohomologyClass.symm (x + y) =
      R.extEquivCohomologyClass.symm x + R.extEquivCohomologyClass.symm y := by
  have := HasDerivedCategory.standard C
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  ext
  simp [← CohomologyClass.mk_add, extEquivCohomologyClass_symm_mk_hom, ShiftedHom.map]

/-- If `R` is an injective resolution of `Y`, then `Ext X Y n` identifies
to the group of cohomology classes of degree `n` from `(singleFunctor C 0).obj X`
to `R.cochainComplex`. -/
@[simps!]
/--
Definition of `extAddEquivCohomologyClass` / `extAddEquivCohomologyClass` 的定义

English:
definition extAddEquivCohomologyClass
  signature: :
  body: AddEquiv.symm
    { toEquiv := (R.extEquivCohomologyClass (X := X) (Y := Y) (n := n)).symm
      map_add' := by simp }

@[simp]

中文:
定义 extAddEquivCohomologyClass
  签名: :
  定义体: AddEquiv.symm
    { toEquiv := (R.extEquivCohomologyClass (X := X) (Y := Y) (n := n)).symm
      map_add' := by simp }

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.symm, R.extEquivCohomologyClass, extEquivCohomologyClass, map_add, toEquiv
-/
noncomputable def extAddEquivCohomologyClass :
    Ext X Y n ≃+ CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n :=
  AddEquiv.symm
    { toEquiv := (R.extEquivCohomologyClass (X := X) (Y := Y) (n := n)).symm
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
    (x y : CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n) :
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
    (x : CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n) :
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
    (R.extEquivCohomologyClass (X := X) (n := n)).symm 0 = 0 :=
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

Depends on / 依赖: F.map, R.extAddEquivCohomologyClass.map_sub, extAddEquivCohomologyClass, map_sub
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
  signature: {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
  body: R.extEquivCohomologyClass.symm
    (.mk (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _)
      m (by lia) (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])))

@[simp]

中文:
定义 extMk
  签名: {n : 自然数} (f : X ⟶ R.cocomplex.X n) (m : 自然数) (hm : n + 1 = m)
  定义体: R.extEquivCohomologyClass.symm
    (.mk (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _)
      m (by lia) (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])))

@[simp]

Depends on / 依赖: Cocycle, Cocycle.fromSingleMk, R.cochainComplexXIso, R.extEquivCohomologyClass.symm, cochainComplexXIso, cochainComplex_d, extEquivCohomologyClass, fromSingleMk, reassoc_of, zero_add
-/
noncomputable def extMk {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    Ext X Y n :=
  R.extEquivCohomologyClass.symm
    (.mk (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _)
      m (by lia) (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])))

@[simp]
/--
lemma `extEquivCohomologyClass_extMk` / 引理 `extEquivCohomologyClass_extMk`

English:
lemma extEquivCohomologyClass_extMk
  statement: {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
  proof: by
  simp [extMk]

中文:
引理 extEquivCohomologyClass_extMk
  结论: {n : 自然数} (f : X ⟶ R.cocomplex.X n) (m : 自然数) (hm : n + 1 = m)
  证明: by
  simp [extMk]
-/
lemma extEquivCohomologyClass_extMk {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    R.extEquivCohomologyClass (R.extMk f m hm hf) =
      (.mk (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _)
        m (by lia) (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf]))) := by
  simp [extMk]

/--
lemma `add_extMk` / 引理 `add_extMk`

English:
lemma add_extMk
  statement: {n : Nat} (f g : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
  proof: by
  simp only [extMk, Preadditive.add_comp]
  rw [Cocycle.fromSingleMk_add _ _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl]; rw [reassoc_of% hf])
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hg])]
  simp

中文:
引理 add_extMk
  结论: {n : 自然数} (f g : X ⟶ R.cocomplex.X n) (m : 自然数) (hm : n + 1 = m)
  证明: by
  simp only [extMk, Preadditive.add_comp]
  rw [Cocycle.fromSingleMk_add _ _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl]; rw [reassoc_of% hf])
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hg])]
  simp

Depends on / 依赖: Cocycle, Cocycle.fromSingleMk_add, Preadditive, Preadditive.add_comp, add_comp, cochainComplex_d, fromSingleMk_add, reassoc_of
-/
lemma add_extMk {n : Nat} (f g : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) (hg : g ≫ R.cocomplex.d n m = 0) :
    R.extMk f m hm hf + R.extMk g m hm hg =
      R.extMk (f + g) m hm (by simp [hf, hg]) := by
  simp only [extMk, Preadditive.add_comp]
  rw [Cocycle.fromSingleMk_add _ _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl]; rw [reassoc_of% hf])
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hg])]
  simp

/--
lemma `sub_extMk` / 引理 `sub_extMk`

English:
lemma sub_extMk
  statement: {n : Nat} (f g : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
  proof: by
  dsimp [extMk]
  simp only [Preadditive.sub_comp]
  rw [Cocycle.fromSingleMk_sub _ _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl]; rw [reassoc_of% hf])
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hg])]
  simp

中文:
引理 sub_extMk
  结论: {n : 自然数} (f g : X ⟶ R.cocomplex.X n) (m : 自然数) (hm : n + 1 = m)
  证明: by
  dsimp [extMk]
  simp only [Preadditive.sub_comp]
  rw [Cocycle.fromSingleMk_sub _ _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl]; rw [reassoc_of% hf])
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hg])]
  simp

Depends on / 依赖: Cocycle, Cocycle.fromSingleMk_sub, Preadditive, Preadditive.sub_comp, cochainComplex_d, fromSingleMk_sub, reassoc_of, sub_comp
-/
lemma sub_extMk {n : Nat} (f g : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) (hg : g ≫ R.cocomplex.d n m = 0) :
    R.extMk f m hm hf - R.extMk g m hm hg =
      R.extMk (f - g) m hm (by simp [hf, hg]) := by
  dsimp [extMk]
  simp only [Preadditive.sub_comp]
  rw [Cocycle.fromSingleMk_sub _ _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl]; rw [reassoc_of% hf])
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hg])]
  simp

/--
lemma `neg_extMk` / 引理 `neg_extMk`

English:
lemma neg_extMk
  statement: {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
  proof: by
  dsimp [extMk]
  simp only [Preadditive.neg_comp]
  rw [Cocycle.fromSingleMk_neg _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl]; rw [reassoc_of% hf])]
  simp

@[simp]

中文:
引理 neg_extMk
  结论: {n : 自然数} (f : X ⟶ R.cocomplex.X n) (m : 自然数) (hm : n + 1 = m)
  证明: by
  dsimp [extMk]
  simp only [Preadditive.neg_comp]
  rw [Cocycle.fromSingleMk_neg _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl]; rw [reassoc_of% hf])]
  simp

@[simp]

Depends on / 依赖: Cocycle, Cocycle.fromSingleMk_neg, Preadditive, Preadditive.neg_comp, cochainComplex_d, fromSingleMk_neg, neg_comp, reassoc_of
-/
lemma neg_extMk {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    -R.extMk f m hm hf = R.extMk (-f) m hm (by simp [hf]) := by
  dsimp [extMk]
  simp only [Preadditive.neg_comp]
  rw [Cocycle.fromSingleMk_neg _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl]; rw [reassoc_of% hf])]
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
    R.extMk (0 : X ⟶ R.cocomplex.X n) m hm (by simp) = 0 := by
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
    [HasDerivedCategory C] {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    (R.extMk f m hm hf).hom =
    (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X)).comp
      ((ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _) m
          (by lia) (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf]))) _).comp
            (.mk₀ _ rfl (inv (DerivedCategory.Q.map R.ι') ≫
              (DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y))
                (zero_add _)) (add_zero _) :=
  extEquivCohomologyClass_symm_mk_hom _ _

/--
lemma `extMk_eq_zero_iff` / 引理 `extMk_eq_zero_iff`

English:
lemma extMk_eq_zero_iff
  statement: (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
  proof: by
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq,
    extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero,
    CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ p (by lia)]; rw [R.cochainComplex_d _ _ _ _ rfl rfl]
  exact ⟨fun ⟨g, hg⟩ => ⟨g 

中文:
引理 extMk_eq_zero_iff
  结论: (f : X ⟶ R.cocomplex.X n) (m : 自然数) (hm : n + 1 = m)
  证明: by
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq,
    extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero,
    CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ p (by lia)]; rw [R.cochainComplex_d _ _ _ _ rfl rfl]
  exact ⟨fun ⟨g, hg⟩ => ⟨g 

Depends on / 依赖: Category, Category.assoc, Cocycle, Cocycle.fromSingleMk_mem_coboundaries_iff, CohomologyClass, CohomologyClass.mk_eq_zero_iff, R.cochainComplexXIso, R.cochainComplex_d, R.extEquivCohomologyClass.apply_eq_iff_eq, apply_eq_iff_eq, cancel_mono, cochainComplexXIso, cochainComplex_d, extEquivCohomologyClass, extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero, fromSingleMk_mem_coboundaries_iff, mk_eq_zero_iff
-/
lemma extMk_eq_zero_iff (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0)
    (p : Nat) (hp : p + 1 = n) :
    R.extMk f m hm hf = 0 ↔
      exists (g : X ⟶ R.cocomplex.X p), g ≫ R.cocomplex.d p n = f := by
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq,
    extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero,
    CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ p (by lia)]; rw [R.cochainComplex_d _ _ _ _ rfl rfl]
  exact ⟨fun ⟨g, hg⟩ => ⟨g ≫ (R.cochainComplexXIso p p rfl).hom,
      by simp only [← cancel_mono (R.cochainComplexXIso n n rfl).inv, Category.assoc, hg]⟩,
    fun ⟨g, hg⟩ => ⟨g ≫ (R.cochainComplexXIso p p rfl).inv, by simp [← hg]⟩⟩

/--
lemma `extMk_surjective` / 引理 `extMk_surjective`

English:
lemma extMk_surjective
  given: (α : Ext X Y n) (m : Nat) (hm : n + 1 = m)
  proof: by
  obtain ⟨x, rfl⟩ := R.extEquivCohomologyClass.symm.surjective α
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective x n (by simp) m (by lia)
  exact ⟨f ≫ (R.cochainComplexXIso n n rfl).hom,
    by simpa [R.cochainComplex_d _ _ _ _ rfl rfl,
      ← cancel

中文:
引理 extMk_surjective
  条件: (α : Ext X Y n) (m : 自然数) (hm : n + 1 = m)
  证明: by
  obtain ⟨x, rfl⟩ := R.extEquivCohomologyClass.symm.surjective α
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective x n (by simp) m (by lia)
  exact ⟨f ≫ (R.cochainComplexXIso n n rfl).hom,
    by simpa [R.cochainComplex_d _ _ _ _ rfl rfl,
      ← cancel

Depends on / 依赖: Cocycle, Cocycle.fromSingleMk_surjective, R.cochainComplexXIso, R.cochainComplex_d, R.extEquivCohomologyClass.symm.surjective, cancel_mono, cochainComplexXIso, cochainComplex_d, extEquivCohomologyClass, fromSingleMk_surjective, mk_surjective, surjective, x.mk_surjective
-/
lemma extMk_surjective (α : Ext X Y n) (m : Nat) (hm : n + 1 = m) :
    exists (f : X ⟶ R.cocomplex.X n) (hf : f ≫ R.cocomplex.d n m = 0),
      R.extMk f m hm hf = α := by
  obtain ⟨x, rfl⟩ := R.extEquivCohomologyClass.symm.surjective α
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective x n (by simp) m (by lia)
  exact ⟨f ≫ (R.cochainComplexXIso n n rfl).hom,
    by simpa [R.cochainComplex_d _ _ _ _ rfl rfl,
      ← cancel_mono (R.cochainComplexXIso m m rfl).inv] using hf, by simp [extMk]⟩

/--
lemma `mk₀_comp_extMk` / 引理 `mk₀_comp_extMk`

English:
lemma mk₀_comp_extMk
  statement: {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
  proof: by
  have := HasDerivedCategory.standard C
  ext
  simp only [extMk, Ext.comp_hom, Int.cast_ofNat_Int, Ext.mk₀_hom,
    extEquivCohomologyClass_symm_mk_hom, Category.assoc]
  rw [Cocycle.fromSingleMk_precomp g _ (zero_add _) _ (by lia) (by
      simp [cochainComplex_d _ _ _ n m rfl rfl]; rw [reassoc

中文:
引理 mk₀_comp_extMk
  结论: {n : 自然数} (f : X ⟶ R.cocomplex.X n) (m : 自然数) (hm : n + 1 = m)
  证明: by
  have := HasDerivedCategory.standard C
  ext
  simp only [extMk, Ext.comp_hom, Int.cast_ofNat_Int, Ext.mk₀_hom,
    extEquivCohomologyClass_symm_mk_hom, Category.assoc]
  rw [Cocycle.fromSingleMk_precomp g _ (zero_add _) _ (by lia) (by
      simp [cochainComplex_d _ _ _ n m rfl rfl]; rw [reassoc

Depends on / 依赖: Category, Category.assoc, Cocycle, Cocycle.equivHomShift_symm_precomp, Cocycle.fromSingleMk_precomp, Ext.comp_hom, Ext.mk, HasDerivedCategory, HasDerivedCategory.standard, Int.cast_ofNat_Int, ShiftedHom, ShiftedHom.comp_assoc, ShiftedHom.map_comp, ShiftedHom.mk, add_zero, cast_ofNat_Int, cochainComplex_d, comp_assoc, comp_hom, equivHomShift_symm_precomp
-/
lemma mk₀_comp_extMk {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) {X' : C} (g : X' ⟶ X) :
    (Ext.mk₀ g).comp (R.extMk f m hm hf) (zero_add _) =
      R.extMk (g ≫ f) m hm (by simp [hf]) := by
  have := HasDerivedCategory.standard C
  ext
  simp only [extMk, Ext.comp_hom, Int.cast_ofNat_Int, Ext.mk₀_hom,
    extEquivCohomologyClass_symm_mk_hom, Category.assoc]
  rw [Cocycle.fromSingleMk_precomp g _ (zero_add _) _ (by lia) (by
      simp [cochainComplex_d _ _ _ n m rfl rfl]; rw [reassoc_of% hf]),
    Cocycle.equivHomShift_symm_precomp, ← ShiftedHom.mk₀_comp 0 rfl,
    ShiftedHom.map_comp,
    ShiftedHom.comp_assoc _ _ _ (add_zero _) (zero_add _) (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (add_zero _) (add_zero (n : Int)) (by simp)]
  simp

variable {R} in
/--
lemma `extMk_comp_mk₀` / 引理 `extMk_comp_mk₀`

English:
lemma extMk_comp_mk₀
  statement: {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
  proof: by
  have := HasDerivedCategory.standard C
  ext
  have : (f ≫ φ.hom.f n) ≫ (R'.cochainComplexXIso n n (by lia)).inv =
      (f ≫ (R.cochainComplexXIso n n (by lia)).inv) ≫ φ.hom'.f n := by
    simp [φ.hom'_f n n rfl]
  simp only [Ext.comp_hom, extMk_hom, Ext.mk₀_hom, this]
  rw [Cocycle.fromSingleM

中文:
引理 extMk_comp_mk₀
  结论: {n : 自然数} (f : X ⟶ R.cocomplex.X n) (m : 自然数) (hm : n + 1 = m)
  证明: by
  have := HasDerivedCategory.standard C
  ext
  have : (f ≫ φ.hom.f n) ≫ (R'.cochainComplexXIso n n (by lia)).inv =
      (f ≫ (R.cochainComplexXIso n n (by lia)).inv) ≫ φ.hom'.f n := by
    simp [φ.hom'_f n n rfl]
  simp only [Ext.comp_hom, extMk_hom, Ext.mk₀_hom, this]
  rw [Cocycle.fromSingleM

Depends on / 依赖: Cocycle, Cocycle.equivHomShift_symm_postcomp, Cocycle.fromSingleMk_postcomp, Ext.comp_hom, Ext.mk, HasDerivedCategory, HasDerivedCategory.standard, R.cochainComplexXIso, R.cochainComplex_d, ShiftedHom, ShiftedHom.comp_assoc, ShiftedHom.comp_mk, ShiftedHom.map_comp, cochainComplexXIso, cochainComplex_d, comp_assoc, comp_hom, equivHomShift_symm_postcomp, extMk_hom, fromSingleMk_postcomp
-/
lemma extMk_comp_mk₀ {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0)
    {Y' : C} {R' : InjectiveResolution Y'} {g : Y ⟶ Y'} (φ : Hom R R' g) :
    (R.extMk f m hm hf).comp (Ext.mk₀ g) (add_zero _) =
      R'.extMk (f ≫ φ.hom.f n) m hm (by simp [reassoc_of% hf]) := by
  have := HasDerivedCategory.standard C
  ext
  have : (f ≫ φ.hom.f n) ≫ (R'.cochainComplexXIso n n (by lia)).inv =
      (f ≫ (R.cochainComplexXIso n n (by lia)).inv) ≫ φ.hom'.f n := by
    simp [φ.hom'_f n n rfl]
  simp only [Ext.comp_hom, extMk_hom, Ext.mk₀_hom, this]
  rw [Cocycle.fromSingleMk_postcomp _ (zero_add _) _ (by lia)
      (by simp [R.cochainComplex_d _ _ _ _ rfl rfl]; rw [reassoc_of% hf]),
    Cocycle.equivHomShift_symm_postcomp,
    ← ShiftedHom.comp_mk₀ _ 0 rfl, ShiftedHom.map_comp,
    ShiftedHom.comp_assoc _ _ _ _ (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ _ (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ _ (zero_add _) (by simp),
    ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀]
  congr 3
  rw [Category.assoc]; rw [← NatTrans.naturality]; rw [← Category.assoc]; rw [← Category.assoc]
  congr 1
  simpa only [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq,
    Functor.map_comp] using! DerivedCategory.Q.congr_map φ.ι'_comp_hom'.symm

end CategoryTheory.InjectiveResolution
