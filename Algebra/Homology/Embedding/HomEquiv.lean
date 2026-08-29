/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.Boundary
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Relations between `extend` and `restriction`

Given an embedding `e : Embedding c c'` of complex shapes satisfying `e.IsRelIff`,
we obtain a bijection `e.homEquiv` between the type of morphisms
`K ⟶ L.extend e` (with `K : HomologicalComplex C c'` and `L : HomologicalComplex C c`)
and the subtype of morphisms `φ : K.restriction e ⟶ L` which satisfy a certain
condition `e.HasLift φ`.

## TODO
* obtain dual results for morphisms `L.extend e ⟶ K`.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace ComplexShape

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

namespace Embedding

open HomologicalComplex

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

section

/--
Definition of `HasLift` / `HasLift` 的定义

English:
definition HasLift
  signature: (φ : K.restriction e ⟶ L)
  body: forall (j : ι) (_ : e.BoundaryGE j) (i' : ι')
    (_ : c'.Rel i' (e.f j)), K.d i' _ ≫ φ.f j = 0

中文:
定义 有Lift
  签名: (φ : K.restriction e ⟶ L)
  定义体: forall (j : ι) (_ : e.BoundaryGE j) (i' : ι')
    (_ : c'.Rel i' (e.f j)), K.d i' _ ≫ φ.f j = 0

Depends on / 依赖: BoundaryGE, Injective, Injective.isZero_under, K.isZero_of_isStrictlyGE, e.BoundaryGE, isStrictlyGE_iff, isZero_of_isStrictlyGE, isZero_under
-/
def HasLift (φ : K.restriction e ⟶ L) : Prop :=
  forall (j : ι) (_ : e.BoundaryGE j) (i' : ι')
    (_ : c'.Rel i' (e.f j)), K.d i' _ ≫ φ.f j = 0

namespace liftExtend

variable (φ : K.restriction e ⟶ L)

variable {e}

open scoped Classical in
/--
Definition of `f` / `f` 的定义

English:
definition f
  signature: (i' : ι')
  body: if hi' : exists i, e.f i = i' then
    (K.restrictionXIso e hi'.choose_spec).inv ≫ φ.f hi'.choose ≫
      (L.extendXIso e hi'.choose_spec).inv
  else 0

中文:
定义 f
  签名: (i' : ι')
  定义体: if hi' : exists i, e.f i = i' then
    (K.restrictionXIso e hi'.choose_spec).inv ≫ φ.f hi'.choose ≫
      (L.extendXIso e hi'.choose_spec).inv
  else 0

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplex, HomologicalComplex.eval, HomologicalComplex.eval_obj, IsZero, IsZero.of_iso, K.restrictionXIso, L.extendXIso, L.isZero_of_isStrictlyGE, all_goals, biprod_isZero_iff, choose_spec, eval_obj, extendXIso, isStrictlyGE_iff, isZero_X_iff, isZero_of_isStrictlyGE, mapBiprod, mappingCone
-/
noncomputable def f (i' : ι') : K.X i' ⟶ (L.extend e).X i' :=
  if hi' : exists i, e.f i = i' then
    (K.restrictionXIso e hi'.choose_spec).inv ≫ φ.f hi'.choose ≫
      (L.extendXIso e hi'.choose_spec).inv
  else 0

/--
lemma `f_eq` / 引理 `f_eq`

English:
lemma f_eq
  given: {i' : ι'} {i : ι} (hi : e.f i = i')
  proof: by
  have hi' : exists k, e.f k = i' := ⟨i, hi⟩
  have : hi'.choose = i := e.injective_f (by rw [hi'.choose_spec, hi])
  grind [f]

中文:
引理 f_eq
  条件: {i' : ι'} {i : ι} (hi : e.f i = i')
  证明: by
  have hi' : exists k, e.f k = i' := ⟨i, hi⟩
  have : hi'.choose = i := e.injective_f (by rw [hi'.choose_spec, hi])
  grind [f]

Depends on / 依赖: choose_spec, e.injective_f, injective_f
-/
lemma f_eq {i' : ι'} {i : ι} (hi : e.f i = i') :
    f φ i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫ (L.extendXIso e hi).inv := by
  have hi' : exists k, e.f k = i' := ⟨i, hi⟩
  have : hi'.choose = i := e.injective_f (by rw [hi'.choose_spec, hi])
  grind [f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `comm` / 引理 `comm`

English:
lemma comm
  given: (hφ : e.HasLift φ) (i' j' : ι')
  proof: by
  by_cases hij' : c'.Rel i' j'
  · by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      rw [f_eq φ hi]
      by_cases hj' : exists j, e.f j = j'
      · obtain ⟨j, hj⟩ := hj'
        rw [f_eq φ hj]; rw [L.extend_d_eq e hi hj]
        subst hi hj
        simp [HomologicalComplex.restrictionXIso]
      · apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
    · have : (L.extend e).d i' j' = 0 := by
        apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_src
      rw [this]; rw [comp_zero]
      by_cases hj' : exists j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj'
        rw [f_eq φ rfl]
        dsimp [restrictionXIso]
        rw [id_comp]; rw [reassoc_of% (hφ j (e.boundaryGE hij'
          (by simpa using hi')) i' hij')]; rw [zero_comp]
      · have : f φ j' = 0 := by
          apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
        rw [this]; rw [comp_zero]
  · simp [HomologicalComplex.shape _ _ _ hij']

中文:
引理 comm
  条件: (hφ : e.有Lift φ) (i' j' : ι')
  证明: by
  by_cases hij' : c'.Rel i' j'
  · by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      rw [f_eq φ hi]
      by_cases hj' : exists j, e.f j = j'
      · obtain ⟨j, hj⟩ := hj'
        rw [f_eq φ hj]; rw [L.extend_d_eq e hi hj]
        subst hi hj
        simp [HomologicalComplex.restrictionXIso]
      · apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
    · have : (L.extend e).d i' j' = 0 := by
        apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_src
      rw [this]; rw [comp_zero]
      by_cases hj' : exists j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj'
        rw [f_eq φ rfl]
        dsimp [restrictionXIso]
        rw [id_comp]; rw [reassoc_of% (hφ j (e.boundaryGE hij'
          (by simpa using hi')) i' hij')]; rw [zero_comp]
      · have : f φ j' = 0 := by
          apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
        rw [this]; rw [comp_zero]
  · simp [HomologicalComplex.shape _ _ _ hij']

Depends on / 依赖: HomologicalComplex, HomologicalComplex.restrictionXIso, L.extend, L.extend_d_eq, L.isZero_extend_X, comp_zero, eq_of_src, eq_of_tgt, extend, extend_d_eq, f_eq, isZero_extend_X, restrictionXIso
-/
lemma comm (hφ : e.HasLift φ) (i' j' : ι') :
    f φ i' ≫ (L.extend e).d i' j' = K.d i' j' ≫ f φ j' := by
  by_cases hij' : c'.Rel i' j'
  · by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      rw [f_eq φ hi]
      by_cases hj' : exists j, e.f j = j'
      · obtain ⟨j, hj⟩ := hj'
        rw [f_eq φ hj]; rw [L.extend_d_eq e hi hj]
        subst hi hj
        simp [HomologicalComplex.restrictionXIso]
      · apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
    · have : (L.extend e).d i' j' = 0 := by
        apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_src
      rw [this]; rw [comp_zero]
      by_cases hj' : exists j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj'
        rw [f_eq φ rfl]
        dsimp [restrictionXIso]
        rw [id_comp]; rw [reassoc_of% (hφ j (e.boundaryGE hij'
          (by simpa using hi')) i' hij')]; rw [zero_comp]
      · have : f φ j' = 0 := by
          apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
        rw [this]; rw [comp_zero]
  · simp [HomologicalComplex.shape _ _ _ hij']

end liftExtend

variable (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ)

/--
Definition of `liftExtend` / `liftExtend` 的定义

English:
definition liftExtend
  signature: :
  body: liftExtend.f φ i'
  comm' _ _ _ := liftExtend.comm φ hφ _ _

中文:
定义 liftExtend
  签名: :
  定义体: liftExtend.f φ i'
  comm' _ _ _ := liftExtend.comm φ hφ _ _

Depends on / 依赖: liftExtend, liftExtend.f
-/
noncomputable def liftExtend :
    K ⟶ L.extend e where
  f i' := liftExtend.f φ i'
  comm' _ _ _ := liftExtend.comm φ hφ _ _

variable {i' : ι'} {i : ι} (hi : e.f i = i')

/--
lemma `liftExtend_f` / 引理 `liftExtend_f`

English:
lemma liftExtend_f
  proof: by
  apply liftExtend.f_eq

中文:
引理 liftExtend_f
  证明: by
  apply liftExtend.f_eq

Depends on / 依赖: f_eq, i_f_comp, liftExtend, liftExtend.f_eq, mono_of_mono_fac
-/
lemma liftExtend_f :
    (e.liftExtend φ hφ).f i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫
      (L.extendXIso e hi).inv := by
  apply liftExtend.f_eq

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `liftExtendfArrowIso` / `liftExtendfArrowIso` 的定义

English:
definition liftExtendfArrowIso
  signature: :
  body: Arrow.isoMk (K.restrictionXIso e hi).symm (L.extendXIso e hi)
    (by simp [e.liftExtend_f φ hφ hi])

中文:
定义 liftExtendfArrowIso
  签名: :
  定义体: Arrow.isoMk (K.restrictionXIso e hi).symm (L.extendXIso e hi)
    (by simp [e.liftExtend_f φ hφ hi])

Depends on / 依赖: Arrow.isoMk, K.restrictionXIso, L.extendXIso, e.liftExtend_f, extendXIso, liftExtend_f, restrictionXIso
-/
noncomputable def liftExtendfArrowIso :
    Arrow.mk ((e.liftExtend φ hφ).f i') ≅ Arrow.mk (φ.f i) :=
  Arrow.isoMk (K.restrictionXIso e hi).symm (L.extendXIso e hi)
    (by simp [e.liftExtend_f φ hφ hi])

/--
lemma `isIso_liftExtend_f_iff` / 引理 `isIso_liftExtend_f_iff`

English:
lemma isIso_liftExtend_f_iff
  given: (hi : e.f i = i')
  proof: (MorphismProperty.isomorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

中文:
引理 isIso_liftExtend_f_iff
  条件: (hi : e.f i = i')
  证明: (MorphismProperty.isomorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

Depends on / 依赖: MorphismProperty, MorphismProperty.isomorphisms, arrow_mk_iso_iff, e.liftExtendfArrowIso, isomorphisms, liftExtendfArrowIso
-/
lemma isIso_liftExtend_f_iff (hi : e.f i = i') :
    IsIso ((e.liftExtend φ hφ).f i') ↔ IsIso (φ.f i) :=
  (MorphismProperty.isomorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

/--
lemma `mono_liftExtend_f_iff` / 引理 `mono_liftExtend_f_iff`

English:
lemma mono_liftExtend_f_iff
  given: (hi : e.f i = i')
  proof: (MorphismProperty.monomorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

中文:
引理 mono_liftExtend_f_iff
  条件: (hi : e.f i = i')
  证明: (MorphismProperty.monomorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homotopyCofiber.XIsoBiprod, Injective, Injective.of_iso, MorphismProperty, MorphismProperty.monomorphisms, XIsoBiprod, arrow_mk_iso_iff, e.liftExtendfArrowIso, homotopyCofiber, liftExtendfArrowIso, monomorphisms, of_iso
-/
lemma mono_liftExtend_f_iff (hi : e.f i = i') :
    Mono ((e.liftExtend φ hφ).f i') ↔ Mono (φ.f i) :=
  (MorphismProperty.monomorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

/--
lemma `epi_liftExtend_f_iff` / 引理 `epi_liftExtend_f_iff`

English:
lemma epi_liftExtend_f_iff
  given: (hi : e.f i = i')
  proof: (MorphismProperty.epimorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

中文:
引理 epi_liftExtend_f_iff
  条件: (hi : e.f i = i')
  证明: (MorphismProperty.epimorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

Depends on / 依赖: MorphismProperty, MorphismProperty.epimorphisms, arrow_mk_iso_iff, e.liftExtendfArrowIso, epimorphisms, liftExtendfArrowIso
-/
lemma epi_liftExtend_f_iff (hi : e.f i = i') :
    Epi ((e.liftExtend φ hφ).f i') ↔ Epi (φ.f i) :=
  (MorphismProperty.epimorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

end

namespace homRestrict

variable {e}
variable (ψ : K ⟶ L.extend e)

/--
Definition of `f` / `f` 的定义

English:
definition f
  signature: (i : ι)
  body: ψ.f (e.f i) ≫ (L.extendXIso e rfl).hom

中文:
定义 f
  签名: (i : ι)
  定义体: ψ.f (e.f i) ≫ (L.extendXIso e rfl).hom

Depends on / 依赖: L.extendXIso, extendXIso
-/
noncomputable def f (i : ι) : (K.restriction e).X i ⟶ L.X i :=
  ψ.f (e.f i) ≫ (L.extendXIso e rfl).hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `f_eq` / 引理 `f_eq`

English:
lemma f_eq
  given: {i : ι} {i' : ι'} (h : e.f i = i')
  proof: by
  subst h
  simp [f, restrictionXIso]

中文:
引理 f_eq
  条件: {i : ι} {i' : ι'} (h : e.f i = i')
  证明: by
  subst h
  simp [f, restrictionXIso]

Depends on / 依赖: restrictionXIso
-/
lemma f_eq {i : ι} {i' : ι'} (h : e.f i = i') :
    f ψ i = (K.restrictionXIso e h).hom ≫ ψ.f i' ≫ (L.extendXIso e h).hom := by
  subst h
  simp [f, restrictionXIso]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `comm` / 引理 `comm`

English:
lemma comm
  given: (i j : ι)
  proof: by
  dsimp [f]
  simp only [assoc, ← ψ.comm_assoc, L.extend_d_eq e rfl rfl, Iso.inv_hom_id, comp_id]

中文:
引理 comm
  条件: (i j : ι)
  证明: by
  dsimp [f]
  simp only [assoc, ← ψ.comm_assoc, L.extend_d_eq e rfl rfl, Iso.inv_hom_id, comp_id]

Depends on / 依赖: Iso.inv_hom_id, L.extend_d_eq, comm_assoc, comp_id, extend_d_eq, inv_hom_id
-/
lemma comm (i j : ι) :
    f ψ i ≫ L.d i j = K.d (e.f i) (e.f j) ≫ f ψ j := by
  dsimp [f]
  simp only [assoc, ← ψ.comm_assoc, L.extend_d_eq e rfl rfl, Iso.inv_hom_id, comp_id]

end homRestrict

/--
Definition of `homRestrict` / `homRestrict` 的定义

English:
definition homRestrict
  signature: (ψ : K ⟶ L.extend e)
  body: homRestrict.f ψ i

中文:
定义 homRestrict
  签名: (ψ : K ⟶ L.extend e)
  定义体: homRestrict.f ψ i

Depends on / 依赖: homRestrict, homRestrict.f
-/
noncomputable def homRestrict (ψ : K ⟶ L.extend e) : K.restriction e ⟶ L where
  f i := homRestrict.f ψ i

/--
lemma `homRestrict_f` / 引理 `homRestrict_f`

English:
lemma homRestrict_f
  given: (ψ : K ⟶ L.extend e) {i : ι} {i' : ι'} (h : e.f i = i')
  proof: homRestrict.f_eq ψ h

中文:
引理 homRestrict_f
  条件: (ψ : K ⟶ L.extend e) {i : ι} {i' : ι'} (h : e.f i = i')
  证明: homRestrict.f_eq ψ h

Depends on / 依赖: f_eq, homRestrict, homRestrict.f_eq
-/
lemma homRestrict_f (ψ : K ⟶ L.extend e) {i : ι} {i' : ι'} (h : e.f i = i') :
    (e.homRestrict ψ).f i = (K.restrictionXIso e h).hom ≫ ψ.f i' ≫ (L.extendXIso e h).hom :=
  homRestrict.f_eq ψ h

set_option backward.isDefEq.respectTransparency false in
/--
lemma `homRestrict_hasLift` / 引理 `homRestrict_hasLift`

English:
lemma homRestrict_hasLift
  given: (ψ : K ⟶ L.extend e)
  proof: by
  intro j hj i' hij'
  have : (L.extend e).d i' (e.f j) = 0 := by
    apply (L.isZero_extend_X e i' (hj.notMem hij')).eq_of_src
  dsimp [homRestrict]
  rw [homRestrict.f_eq ψ rfl]; rw [restrictionXIso]; rw [eqToIso_refl]; rw [Iso.refl_hom]; rw [id_comp]; rw [← ψ.comm_assoc]; rw [this]; rw [zero_comp]; rw [comp_zero]

@[simp]

中文:
引理 homRestrict_hasLift
  条件: (ψ : K ⟶ L.extend e)
  证明: by
  intro j hj i' hij'
  have : (L.extend e).d i' (e.f j) = 0 := by
    apply (L.isZero_extend_X e i' (hj.notMem hij')).eq_of_src
  dsimp [homRestrict]
  rw [homRestrict.f_eq ψ rfl]; rw [restrictionXIso]; rw [eqToIso_refl]; rw [Iso.refl_hom]; rw [id_comp]; rw [← ψ.comm_assoc]; rw [this]; rw [zero_comp]; rw [comp_zero]

@[simp]

Depends on / 依赖: Iso.refl_hom, L.extend, L.isZero_extend_X, comm_assoc, comp_zero, eqToIso_refl, eq_of_src, extend, f_eq, hj.notMem, homRestrict, homRestrict.f_eq, id_comp, isZero_extend_X, notMem, refl_hom, restrictionXIso, zero_comp
-/
lemma homRestrict_hasLift (ψ : K ⟶ L.extend e) :
    e.HasLift (e.homRestrict ψ) := by
  intro j hj i' hij'
  have : (L.extend e).d i' (e.f j) = 0 := by
    apply (L.isZero_extend_X e i' (hj.notMem hij')).eq_of_src
  dsimp [homRestrict]
  rw [homRestrict.f_eq ψ rfl]; rw [restrictionXIso]; rw [eqToIso_refl]; rw [Iso.refl_hom]; rw [id_comp]; rw [← ψ.comm_assoc]; rw [this]; rw [zero_comp]; rw [comp_zero]

@[simp]
/--
lemma `liftExtend_homRestrict` / 引理 `liftExtend_homRestrict`

English:
lemma liftExtend_homRestrict
  given: (ψ : K ⟶ L.extend e)
  proof: by
  ext i'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    simp [e.homRestrict_f _ rfl, e.liftExtend_f _ _ rfl]
  · apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_tgt

@[simp]

中文:
引理 liftExtend_homRestrict
  条件: (ψ : K ⟶ L.extend e)
  证明: by
  ext i'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    simp [e.homRestrict_f _ rfl, e.liftExtend_f _ _ rfl]
  · apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_tgt

@[simp]

Depends on / 依赖: L.isZero_extend_X, e.homRestrict_f, e.liftExtend_f, eq_of_tgt, homRestrict_f, isZero_extend_X, liftExtend_f
-/
lemma liftExtend_homRestrict (ψ : K ⟶ L.extend e) :
    e.liftExtend (e.homRestrict ψ) (e.homRestrict_hasLift ψ) = ψ := by
  ext i'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    simp [e.homRestrict_f _ rfl, e.liftExtend_f _ _ rfl]
  · apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_tgt

@[simp]
/--
lemma `homRestrict_liftExtend` / 引理 `homRestrict_liftExtend`

English:
lemma homRestrict_liftExtend
  given: (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ)
  proof: by
  ext i
  simp [e.homRestrict_f _ rfl, e.liftExtend_f _ _ rfl]

中文:
引理 homRestrict_liftExtend
  条件: (φ : K.restriction e ⟶ L) (hφ : e.有Lift φ)
  证明: by
  ext i
  simp [e.homRestrict_f _ rfl, e.liftExtend_f _ _ rfl]

Depends on / 依赖: e.homRestrict_f, e.liftExtend_f, homRestrict_f, liftExtend_f
-/
lemma homRestrict_liftExtend (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ) :
    e.homRestrict (e.liftExtend φ hφ) = φ := by
  ext i
  simp [e.homRestrict_f _ rfl, e.liftExtend_f _ _ rfl]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `homRestrict_precomp` / 引理 `homRestrict_precomp`

English:
lemma homRestrict_precomp
  given: (α : K' ⟶ K) (ψ : K ⟶ L.extend e)
  proof: by
  ext i
  simp [homRestrict_f _ _ rfl, restrictionXIso]

@[reassoc]

中文:
引理 homRestrict_precomp
  条件: (α : K' ⟶ K) (ψ : K ⟶ L.extend e)
  证明: by
  ext i
  simp [homRestrict_f _ _ rfl, restrictionXIso]

@[reassoc]

Depends on / 依赖: homRestrict_f, restrictionXIso
-/
lemma homRestrict_precomp (α : K' ⟶ K) (ψ : K ⟶ L.extend e) :
    e.homRestrict (α ≫ ψ) = restrictionMap α e ≫ e.homRestrict ψ := by
  ext i
  simp [homRestrict_f _ _ rfl, restrictionXIso]

@[reassoc]
/--
lemma `homRestrict_comp_extendMap` / 引理 `homRestrict_comp_extendMap`

English:
lemma homRestrict_comp_extendMap
  given: (ψ : K ⟶ L.extend e) (β : L ⟶ L')
  proof: by
  ext i
  simp [homRestrict_f _ _ rfl, extendMap_f β e rfl]

中文:
引理 homRestrict_comp_extendMap
  条件: (ψ : K ⟶ L.extend e) (β : L ⟶ L')
  证明: by
  ext i
  simp [homRestrict_f _ _ rfl, extendMap_f β e rfl]

Depends on / 依赖: extendMap_f, homRestrict_f
-/
lemma homRestrict_comp_extendMap (ψ : K ⟶ L.extend e) (β : L ⟶ L') :
    e.homRestrict (ψ ≫ extendMap β e) =
      e.homRestrict ψ ≫ β := by
  ext i
  simp [homRestrict_f _ _ rfl, extendMap_f β e rfl]

variable (K L)

/-- The bijection between `K ⟶ L.extend e` and the subtype of `K.restriction e ⟶ L`
consisting of morphisms `φ` such that `e.HasLift φ`. -/
@[simps]
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: :
  body: ⟨e.homRestrict ψ, e.homRestrict_hasLift ψ⟩
  invFun φ := e.liftExtend φ.1 φ.2
  left_inv ψ := by simp
  right_inv φ := by simp

中文:
定义 homEquiv
  签名: :
  定义体: ⟨e.homRestrict ψ, e.homRestrict_hasLift ψ⟩
  invFun φ := e.liftExtend φ.1 φ.2
  left_inv ψ := by simp
  right_inv φ := by simp

Depends on / 依赖: e.homRestrict, e.homRestrict_hasLift, homRestrict, homRestrict_hasLift
-/
noncomputable def homEquiv :
    (K ⟶ L.extend e) ≃ { φ : K.restriction e ⟶ L // e.HasLift φ } where
  toFun ψ := ⟨e.homRestrict ψ, e.homRestrict_hasLift ψ⟩
  invFun φ := e.liftExtend φ.1 φ.2
  left_inv ψ := by simp
  right_inv φ := by simp

end Embedding

end ComplexShape
