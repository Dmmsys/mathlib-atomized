/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.InducedShiftSequence
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Compatibilities of the homology functor with the shift

This file studies how homology of cochain complexes behaves with respect to
the shift: there is a natural isomorphism `(K⟦n⟧).homology a ≅ K.homology a`
when `n + a = a'`. This is summarized by instances
`(homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ` in the `CochainComplex`
and `HomotopyCategory` namespaces.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category ComplexShape Limits

variable (C : Type*) [Category* C] [Preadditive C]

namespace CochainComplex

open HomologicalComplex

attribute [local simp] XIsoOfEq_hom_naturality smul_smul

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `(K⟦n⟧).sc' i j k ≅ K.sc' i' j' k'` when `n + i = i'`,
`n + j = j'` and `n + k = k'`. -/
@[simps!]
/--
Definition of `shiftShortComplexFunctor'` / `shiftShortComplexFunctor'` 的定义

English:
definition shiftShortComplexFunctor'
  signature: (n i j k i' j' k' : Int)
  body: NatIso.ofComponents (fun K => ShortComplex.isoMk
      (n.negOnePow • ((shiftEval C n i i' hi).app K))
      ((shiftEval C n j j' hj).app K) (n.negOnePow • ((shiftEval C n k k' hk).app K))
      (by simp) (by simp))
      (fun f => by ext <;> simp)

中文:
定义 shiftShortComplexFunctor'
  签名: (n i j k i' j' k' : 整数)
  定义体: NatIso.ofComponents (fun K => ShortComplex.isoMk
      (n.negOnePow • ((shiftEval C n i i' hi).app K))
      ((shiftEval C n j j' hj).app K) (n.negOnePow • ((shiftEval C n k k' hk).app K))
      (by simp) (by simp))
      (fun f => by ext <;> simp)

Depends on / 依赖: NatIso, NatIso.ofComponents, ShortComplex, ShortComplex.isoMk, n.negOnePow, negOnePow, ofComponents, shiftEval
-/
def shiftShortComplexFunctor' (n i j k i' j' k' : Int)
    (hi : n + i = i') (hj : n + j = j') (hk : n + k = k') :
    (CategoryTheory.shiftFunctor (CochainComplex C Int) n) ⋙ shortComplexFunctor' C _ i j k ≅
      shortComplexFunctor' C _ i' j' k' :=
  NatIso.ofComponents (fun K => ShortComplex.isoMk
      (n.negOnePow • ((shiftEval C n i i' hi).app K))
      ((shiftEval C n j j' hj).app K) (n.negOnePow • ((shiftEval C n k k' hk).app K))
      (by simp) (by simp))
      (fun f => by ext <;> simp)

/-- The natural isomorphism `(K⟦n⟧).sc i ≅ K.sc i'` when `n + i = i'`. -/
@[simps!]
/--
Definition of `shiftShortComplexFunctorIso` / `shiftShortComplexFunctorIso` 的定义

English:
definition shiftShortComplexFunctorIso
  signature: (n i i' : Int) (hi : n + i = i')
  body: shiftShortComplexFunctor' C n _ i _ _ i' _
    (by simp only [prev]; lia) hi (by simp only [next]; lia)

中文:
定义 shiftShortComplexFunctorIso
  签名: (n i i' : 整数) (hi : n + i = i')
  定义体: shiftShortComplexFunctor' C n _ i _ _ i' _
    (by simp only [prev]; lia) hi (by simp only [next]; lia)

Depends on / 依赖: shiftShortComplexFunctor
-/
noncomputable def shiftShortComplexFunctorIso (n i i' : Int) (hi : n + i = i') :
    shiftFunctor C n ⋙ shortComplexFunctor C _ i ≅ shortComplexFunctor C _ i' :=
  shiftShortComplexFunctor' C n _ i _ _ i' _
    (by simp only [prev]; lia) hi (by simp only [next]; lia)

variable {C}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `shiftShortComplexFunctorIso_zero_add_hom_app` / 引理 `shiftShortComplexFunctorIso_zero_add_hom_app`

English:
lemma shiftShortComplexFunctorIso_zero_add_hom_app
  given: (a : Int) (K : CochainComplex C Int)
  proof: by
  ext <;> simp [one_smul, shiftFunctorZero_hom_app_f]

中文:
引理 shiftShortComplexFunctorIso_zero_add_hom_app
  条件: (a : 整数) (K : 上链复形 C 整数)
  证明: by
  ext <;> simp [one_smul, shiftFunctorZero_hom_app_f]

Depends on / 依赖: one_smul, shiftFunctorZero_hom_app_f
-/
lemma shiftShortComplexFunctorIso_zero_add_hom_app (a : Int) (K : CochainComplex C Int) :
    (shiftShortComplexFunctorIso C 0 a a (zero_add a)).hom.app K =
      (shortComplexFunctor C (ComplexShape.up Int) a).map
        ((shiftFunctorZero (CochainComplex C Int) Int).hom.app K) := by
  ext <;> simp [one_smul, shiftFunctorZero_hom_app_f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `shiftShortComplexFunctorIso_add'_hom_app` / 引理 `shiftShortComplexFunctorIso_add'_hom_app`

English:
lemma shiftShortComplexFunctorIso_add'_hom_app
  proof: by
  ext <;> dsimp <;> simp only [← hmn, Int.negOnePow_add, shiftFunctorAdd'_hom_app_f',
    XIsoOfEq_shift, Linear.comp_units_smul, Linear.units_smul_comp,
    XIsoOfEq_hom_comp_XIsoOfEq_hom, smul_smul]

中文:
引理 shiftShortComplexFunctorIso_add'_hom_app
  证明: by
  ext <;> dsimp <;> simp only [← hmn, Int.negOnePow_add, shiftFunctorAdd'_hom_app_f',
    XIsoOfEq_shift, Linear.comp_units_smul, Linear.units_smul_comp,
    XIsoOfEq_hom_comp_XIsoOfEq_hom, smul_smul]

Depends on / 依赖: Int.negOnePow_add, Linear, Linear.comp_units_smul, Linear.units_smul_comp, XIsoOfEq_hom_comp_XIsoOfEq_hom, XIsoOfEq_shift, _hom_app_f, comp_units_smul, negOnePow_add, shiftFunctorAdd, smul_smul, units_smul_comp
-/
lemma shiftShortComplexFunctorIso_add'_hom_app
    (n m mn : Int) (hmn : m + n = mn) (a a' a'' : Int) (ha' : n + a = a') (ha'' : m + a' = a'')
    (K : CochainComplex C Int) :
    (shiftShortComplexFunctorIso C mn a a'' (by rw [← ha'', ← ha', ← add_assoc, hmn])).hom.app K =
      (shortComplexFunctor C (ComplexShape.up Int) a).map
        ((CategoryTheory.shiftFunctorAdd' (CochainComplex C Int) m n mn hmn).hom.app K) ≫
        (shiftShortComplexFunctorIso C n a a' ha').hom.app (K⟦m⟧) ≫
        (shiftShortComplexFunctorIso C m a' a'' ha'').hom.app K := by
  ext <;> dsimp <;> simp only [← hmn, Int.negOnePow_add, shiftFunctorAdd'_hom_app_f',
    XIsoOfEq_shift, Linear.comp_units_smul, Linear.units_smul_comp,
    XIsoOfEq_hom_comp_XIsoOfEq_hom, smul_smul]

variable [CategoryWithHomology C]

namespace ShiftSequence

variable (C) in
/--
Definition of `shiftIso` / `shiftIso` 的定义

English:
definition shiftIso
  signature: (n a a' : Int) (ha' : n + a = a')
  body: Functor.isoWhiskerLeft _ (homologyFunctorIso C (ComplexShape.up Int) a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (shiftShortComplexFunctorIso C n a a' ha')
      (ShortComplex.homologyFunctor C) ≪≫
    (homologyFunctorIso C (ComplexShape.up Int) a').symm

中文:
定义 shiftIso
  签名: (n a a' : 整数) (ha' : n + a = a')
  定义体: Functor.isoWhiskerLeft _ (homologyFunctorIso C (ComplexShape.up Int) a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (shiftShortComplexFunctorIso C n a a' ha')
      (ShortComplex.homologyFunctor C) ≪≫
    (homologyFunctorIso C (ComplexShape.up Int) a').symm

Depends on / 依赖: ComplexShape, ComplexShape.up, Functor, Functor.associator, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, ShortComplex, ShortComplex.homologyFunctor, associator, homologyFunctor, homologyFunctorIso, isoWhiskerLeft, isoWhiskerRight, shiftShortComplexFunctorIso
-/
noncomputable def shiftIso (n a a' : Int) (ha' : n + a = a') :
    (CategoryTheory.shiftFunctor _ n) ⋙ homologyFunctor C (ComplexShape.up Int) a ≅
      homologyFunctor C (ComplexShape.up Int) a' :=
  Functor.isoWhiskerLeft _ (homologyFunctorIso C (ComplexShape.up Int) a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (shiftShortComplexFunctorIso C n a a' ha')
      (ShortComplex.homologyFunctor C) ≪≫
    (homologyFunctorIso C (ComplexShape.up Int) a').symm

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftIso_hom_app` / 引理 `shiftIso_hom_app`

English:
lemma shiftIso_hom_app
  given: (n a a' : Int) (ha' : n + a = a') (K : CochainComplex C Int)
  proof: by
  simp [shiftIso, HomologicalComplex.homology]

中文:
引理 shiftIso_hom_app
  条件: (n a a' : 整数) (ha' : n + a = a') (K : 上链复形 C 整数)
  证明: by
  simp [shiftIso, HomologicalComplex.homology]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homology, homology, shiftIso
-/
lemma shiftIso_hom_app (n a a' : Int) (ha' : n + a = a') (K : CochainComplex C Int) :
    (shiftIso C n a a' ha').hom.app K =
      ShortComplex.homologyMap ((shiftShortComplexFunctorIso C n a a' ha').hom.app K) := by
  simp [shiftIso, HomologicalComplex.homology]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftIso_inv_app` / 引理 `shiftIso_inv_app`

English:
lemma shiftIso_inv_app
  given: (n a a' : Int) (ha' : n + a = a') (K : CochainComplex C Int)
  proof: by
  simp [shiftIso, HomologicalComplex.homology]

中文:
引理 shiftIso_inv_app
  条件: (n a a' : 整数) (ha' : n + a = a') (K : 上链复形 C 整数)
  证明: by
  simp [shiftIso, HomologicalComplex.homology]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homology, homology, shiftIso
-/
lemma shiftIso_inv_app (n a a' : Int) (ha' : n + a = a') (K : CochainComplex C Int) :
    (shiftIso C n a a' ha').inv.app K =
      ShortComplex.homologyMap ((shiftShortComplexFunctorIso C n a a' ha').inv.app K) := by
  simp [shiftIso, HomologicalComplex.homology]

end ShiftSequence

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: homologyFunctor C (ComplexShape.up Int) n
  isoZero := Iso.refl _
  shiftIso n a a' ha' := ShiftSequence.shiftIso C n a a' ha'
  shiftIso_zero a := by
    ext K
    dsimp [homologyMap]
    simp only [ShiftSequence.shiftIso_hom_app, comp_id,
      shiftShortComplexFunctorIso_zero_add_hom_app]
  shift

中文:
实例 :
  定义体: homologyFunctor C (ComplexShape.up Int) n
  isoZero := Iso.refl _
  shiftIso n a a' ha' := ShiftSequence.shiftIso C n a a' ha'
  shiftIso_zero a := by
    ext K
    dsimp [homologyMap]
    simp only [ShiftSequence.shiftIso_hom_app, comp_id,
      shiftShortComplexFunctorIso_zero_add_hom_app]
  shift

Depends on / 依赖: ComplexShape, ComplexShape.up, homologyFunctor
-/
noncomputable instance :
    (homologyFunctor C (ComplexShape.up Int) 0).ShiftSequence Int where
  sequence n := homologyFunctor C (ComplexShape.up Int) n
  isoZero := Iso.refl _
  shiftIso n a a' ha' := ShiftSequence.shiftIso C n a a' ha'
  shiftIso_zero a := by
    ext K
    dsimp [homologyMap]
    simp only [ShiftSequence.shiftIso_hom_app, comp_id,
      shiftShortComplexFunctorIso_zero_add_hom_app]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext K
    dsimp [homologyMap]
    simp only [ShiftSequence.shiftIso_hom_app, id_comp,
      ← ShortComplex.homologyMap_comp, shiftFunctorAdd'_eq_shiftFunctorAdd,
      shiftShortComplexFunctorIso_add'_hom_app n m _ rfl a a' a'' ha' ha'' K]

/--
lemma `quasiIsoAt_shift_iff` / 引理 `quasiIsoAt_shift_iff`

English:
lemma quasiIsoAt_shift_iff
  given: {K L : CochainComplex C Int} (φ : K ⟶ L) (n i j : Int) (h : n + i = j)
  proof: by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (NatIso.isIso_map_iff
    ((homologyFunctor C (ComplexShape.up Int) 0).shiftIso n i j h) φ)

中文:
引理 quasiIsoAt_shift_iff
  条件: {K L : 上链复形 C 整数} (φ : K ⟶ L) (n i j : 整数) (h : n + i = j)
  证明: by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (NatIso.isIso_map_iff
    ((homologyFunctor C (ComplexShape.up Int) 0).shiftIso n i j h) φ)

Depends on / 依赖: ComplexShape, ComplexShape.up, NatIso, NatIso.isIso_map_iff, homologyFunctor, isIso_map_iff, quasiIsoAt_iff_isIso_homologyMap, shiftIso
-/
lemma quasiIsoAt_shift_iff {K L : CochainComplex C Int} (φ : K ⟶ L) (n i j : Int) (h : n + i = j) :
    QuasiIsoAt (φ⟦n⟧') i ↔ QuasiIsoAt φ j := by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (NatIso.isIso_map_iff
    ((homologyFunctor C (ComplexShape.up Int) 0).shiftIso n i j h) φ)

/--
lemma `quasiIso_shift_iff` / 引理 `quasiIso_shift_iff`

English:
lemma quasiIso_shift_iff
  given: {K L : CochainComplex C Int} (φ : K ⟶ L) (n : Int)
  proof: by
  simp only [quasiIso_iff, fun i => quasiIsoAt_shift_iff φ n i _ rfl]
  constructor
  · intro h j
    obtain ⟨i, rfl⟩ : exists i, j = n + i := ⟨j - n, by lia⟩
    exact h i
  · intro h i
    exact h (n + i)

中文:
引理 quasiIso_shift_iff
  条件: {K L : 上链复形 C 整数} (φ : K ⟶ L) (n : 整数)
  证明: by
  simp only [quasiIso_iff, fun i => quasiIsoAt_shift_iff φ n i _ rfl]
  constructor
  · intro h j
    obtain ⟨i, rfl⟩ : exists i, j = n + i := ⟨j - n, by lia⟩
    exact h i
  · intro h i
    exact h (n + i)

Depends on / 依赖: quasiIsoAt_shift_iff, quasiIso_iff
-/
lemma quasiIso_shift_iff {K L : CochainComplex C Int} (φ : K ⟶ L) (n : Int) :
    QuasiIso (φ⟦n⟧') ↔ QuasiIso φ := by
  simp only [quasiIso_iff, fun i => quasiIsoAt_shift_iff φ n i _ rfl]
  constructor
  · intro h j
    obtain ⟨i, rfl⟩ : exists i, j = n + i := ⟨j - n, by lia⟩
    exact h i
  · intro h i
    exact h (n + i)

instance {K L : CochainComplex C Int} (φ : K ⟶ L) (n : Int) [QuasiIso φ] :
    QuasiIso (φ⟦n⟧') := by
  rw [quasiIso_shift_iff]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (HomologicalComplex.quasiIso C (ComplexShape.up Int)).IsCompatibleWithShift Int
  body: by ext; apply quasiIso_shift_iff

中文:
实例 :
  签名: (同调复形.quasiIso C (余mplexShape.up 整数)).是余mpatibleWithShift 整数
  定义体: by ext; apply quasiIso_shift_iff

Depends on / 依赖: quasiIso_shift_iff
-/
instance : (HomologicalComplex.quasiIso C (ComplexShape.up Int)).IsCompatibleWithShift Int where
  condition n := by ext; apply quasiIso_shift_iff

variable (C) in
/--
lemma `homologyFunctor_shift` / 引理 `homologyFunctor_shift`

English:
lemma homologyFunctor_shift
  given: (n : Int)
  proof: rfl

中文:
引理 homologyFunctor_shift
  条件: (n : 整数)
  证明: rfl
-/
lemma homologyFunctor_shift (n : Int) :
    (homologyFunctor C (ComplexShape.up Int) 0).shift n =
      homologyFunctor C (ComplexShape.up Int) n := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `liftCycles_shift_homologyπ` / 引理 `liftCycles_shift_homologyπ`

English:
lemma liftCycles_shift_homologyπ
  proof: by
  simp only [liftCycles, homologyπ,
    shiftFunctorObjXIso, Functor.shiftIso, Functor.ShiftSequence.shiftIso,
    ShiftSequence.shiftIso_inv_app, ShortComplex.homologyπ_naturality,
    ShortComplex.liftCycles_comp_cyclesMap_assoc, shiftShortComplexFunctorIso_inv_app_τ₂,
    assoc, Iso.hom_inv_id

中文:
引理 liftCycles_shift_homologyπ
  证明: by
  simp only [liftCycles, homologyπ,
    shiftFunctorObjXIso, Functor.shiftIso, Functor.ShiftSequence.shiftIso,
    ShiftSequence.shiftIso_inv_app, ShortComplex.homologyπ_naturality,
    ShortComplex.liftCycles_comp_cyclesMap_assoc, shiftShortComplexFunctorIso_inv_app_τ₂,
    assoc, Iso.hom_inv_id

Depends on / 依赖: Functor, Functor.ShiftSequence.shiftIso, Functor.shiftIso, HomologicalComplex, HomologicalComplex.homologyFunctor, Int.units_mul_self, K.homology, Linear, Linear.comp_units_smul, ShiftSequence, ShiftSequence.shiftIso_inv_app, ShortComplex, ShortComplex.homology, comp_id, comp_units_smul, homologyFunctor, inv.app, liftCycles, mul_smul, n.negOnePow
-/
lemma liftCycles_shift_homologyπ
    (K : CochainComplex C Int) {A : C} {n i : Int} (f : A ⟶ (K⟦n⟧).X i) (j : Int)
    (hj : (up Int).next i = j) (hf : f ≫ (K⟦n⟧).d i j = 0) (i' : Int) (hi' : n + i = i') (j' : Int)
    (hj' : (up Int).next i' = j') :
    (K⟦n⟧).liftCycles f j hj hf ≫ (K⟦n⟧).homologyπ i =
      K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' (by lia)).hom) j' hj' (by
        simp only [next] at hj hj'
        obtain rfl : i' = i + n := by lia
        obtain rfl : j' = j + n := by lia
        dsimp at hf ⊢
        simp only [Linear.comp_units_smul] at hf
        apply (one_smul (M := Intˣ) _).symm.trans _
        rw [← Int.units_mul_self n.negOnePow]; rw [mul_smul]; rw [comp_id]; rw [hf]; rw [smul_zero]) ≫
        K.homologyπ i' ≫
          ((HomologicalComplex.homologyFunctor C (up Int) 0).shiftIso n i i' hi').inv.app K := by
  simp only [liftCycles, homologyπ,
    shiftFunctorObjXIso, Functor.shiftIso, Functor.ShiftSequence.shiftIso,
    ShiftSequence.shiftIso_inv_app, ShortComplex.homologyπ_naturality,
    ShortComplex.liftCycles_comp_cyclesMap_assoc, shiftShortComplexFunctorIso_inv_app_τ₂,
    assoc, Iso.hom_inv_id, comp_id]
  rfl

end CochainComplex

namespace HomotopyCategory

variable [CategoryWithHomology C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: Functor.ShiftSequence.induced (homologyFunctorFactors C (ComplexShape.up Int) 0) Int
    (homologyFunctor C (ComplexShape.up Int))
    (homologyFunctorFactors C (ComplexShape.up Int))

中文:
实例 :
  定义体: Functor.ShiftSequence.induced (homologyFunctorFactors C (ComplexShape.up Int) 0) Int
    (homologyFunctor C (ComplexShape.up Int))
    (homologyFunctorFactors C (ComplexShape.up Int))

Depends on / 依赖: ComplexShape, ComplexShape.up, Functor, Functor.ShiftSequence.induced, ShiftSequence, homologyFunctor, homologyFunctorFactors, induced
-/
noncomputable instance :
    (homologyFunctor C (ComplexShape.up Int) 0).ShiftSequence Int :=
  Functor.ShiftSequence.induced (homologyFunctorFactors C (ComplexShape.up Int) 0) Int
    (homologyFunctor C (ComplexShape.up Int))
    (homologyFunctorFactors C (ComplexShape.up Int))

variable {C}

/--
lemma `homologyShiftIso_hom_app` / 引理 `homologyShiftIso_hom_app`

English:
lemma homologyShiftIso_hom_app
  given: (n a a' : Int) (ha' : n + a = a') (K : CochainComplex C Int)
  proof: by
  apply Functor.ShiftSequence.induced_shiftIso_hom_app_obj

@[reassoc]

中文:
引理 homologyShiftIso_hom_app
  条件: (n a a' : 整数) (ha' : n + a = a') (K : 上链复形 C 整数)
  证明: by
  apply Functor.ShiftSequence.induced_shiftIso_hom_app_obj

@[reassoc]

Depends on / 依赖: Functor, Functor.ShiftSequence.induced_shiftIso_hom_app_obj, ShiftSequence, induced_shiftIso_hom_app_obj
-/
lemma homologyShiftIso_hom_app (n a a' : Int) (ha' : n + a = a') (K : CochainComplex C Int) :
    ((homologyFunctor C (ComplexShape.up Int) 0).shiftIso n a a' ha').hom.app
      ((quotient _ _).obj K) =
    (homologyFunctor _ _ a).map (((quotient _ _).commShiftIso n).inv.app K) ≫
      (homologyFunctorFactors _ _ a).hom.app (K⟦n⟧) ≫
      ((HomologicalComplex.homologyFunctor _ _ 0).shiftIso n a a' ha').hom.app K ≫
      (homologyFunctorFactors _ _ a').inv.app K := by
  apply Functor.ShiftSequence.induced_shiftIso_hom_app_obj

@[reassoc]
/--
lemma `homologyFunctor_shiftMap` / 引理 `homologyFunctor_shiftMap`

English:
lemma homologyFunctor_shiftMap
  proof: by
  apply Functor.ShiftSequence.induced_shiftMap

中文:
引理 homologyFunctor_shiftMap
  证明: by
  apply Functor.ShiftSequence.induced_shiftMap

Depends on / 依赖: Functor, Functor.ShiftSequence.induced_shiftMap, ShiftSequence, induced_shiftMap
-/
lemma homologyFunctor_shiftMap
    {K L : CochainComplex C Int} {n : Int} (f : K ⟶ L⟦n⟧) (a a' : Int) (h : n + a = a') :
    (homologyFunctor C (ComplexShape.up Int) 0).shiftMap
      (ShiftedHom.map f (quotient _ _)) a a' h =
        (homologyFunctorFactors _ _ a).hom.app K ≫
          (HomologicalComplex.homologyFunctor C (ComplexShape.up Int) 0).shiftMap f a a' h ≫
            (homologyFunctorFactors _ _ a').inv.app L := by
  apply Functor.ShiftSequence.induced_shiftMap

end HomotopyCategory
