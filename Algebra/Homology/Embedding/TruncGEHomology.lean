/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.TruncGE
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-! # The homology of a canonical truncation

Given an embedding of complex shapes `e : Embedding c c'`,
we relate the homology of `K : HomologicalComplex C c'` and of
`K.truncGE e : HomologicalComplex C c'`.

The main result is that `K.πTruncGE e : K ⟶ K.truncGE e` induces a
quasi-isomorphism in degree `e.f i` for all `i`. (Note that the complex
`K.truncGE e` is exact in degrees that are not in the image of `e.f`.)

-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c') [e.IsTruncGE]
  [forall i', K.HasHomology i'] [forall i', L.HasHomology i']

namespace truncGE'

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hi hk in
/--
lemma `hasHomology_sc'_of_not_mem_boundary` / 引理 `hasHomology_sc'_of_not_mem_boundary`

English:
lemma hasHomology_sc'_of_not_mem_boundary
  given: (hj : ¬ e.BoundaryGE j)
  proof: by
  have : (K.restriction e).HasHomology j :=
    restriction.hasHomology K e i j k hi hk rfl rfl rfl
      (e.prev_f_of_not_boundaryGE hi hj) (e.next_f hk)
  have := ShortComplex.hasHomology_of_iso ((K.restriction e).isoSc' i j k hi hk)
  let φ := (shortComplexFunctor' C c i j k).map (K.restrictio

中文:
引理 hasHomology_sc'_of_not_mem_boundary
  条件: (hj : ¬ e.BoundaryGE j)
  证明: by
  have : (K.restriction e).HasHomology j :=
    restriction.hasHomology K e i j k hi hk rfl rfl rfl
      (e.prev_f_of_not_boundaryGE hi hj) (e.next_f hk)
  have := ShortComplex.hasHomology_of_iso ((K.restriction e).isoSc' i j k hi hk)
  let φ := (shortComplexFunctor' C c i j k).map (K.restrictio

Depends on / 依赖: HasHomology, K.isIso_restrictionToTruncGE, K.restriction, K.restrictionToTruncGE, ShortComplex, ShortComplex.hasHomology_of_iso, e.next_f, e.not_boundaryGE_next, e.prev_f_of_not_boundaryGE, hasHomology, hasHomology_of_iso, infer_instance, isIso_restrictionToTruncGE, next_f, not_boundaryGE_next, prev_f_of_not_boundaryGE, restriction, restriction.hasHomology, restrictionToTruncGE, shortComplexFunctor
-/
lemma hasHomology_sc'_of_not_mem_boundary (hj : ¬ e.BoundaryGE j) :
    ((K.truncGE' e).sc' i j k).HasHomology := by
  have : (K.restriction e).HasHomology j :=
    restriction.hasHomology K e i j k hi hk rfl rfl rfl
      (e.prev_f_of_not_boundaryGE hi hj) (e.next_f hk)
  have := ShortComplex.hasHomology_of_iso ((K.restriction e).isoSc' i j k hi hk)
  let φ := (shortComplexFunctor' C c i j k).map (K.restrictionToTruncGE' e)
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := K.isIso_restrictionToTruncGE' e j hj
  have : IsIso φ.τ₃ := K.isIso_restrictionToTruncGE' e k (e.not_boundaryGE_next' hj hk)
  exact ShortComplex.hasHomology_of_epi_of_isIso_of_mono φ

/--
lemma `hasHomology_of_not_mem_boundary` / 引理 `hasHomology_of_not_mem_boundary`

English:
lemma hasHomology_of_not_mem_boundary
  given: (hj : ¬ e.BoundaryGE j)
  proof: hasHomology_sc'_of_not_mem_boundary K e _ j _ rfl rfl hj

中文:
引理 hasHomology_of_not_mem_boundary
  条件: (hj : ¬ e.BoundaryGE j)
  证明: hasHomology_sc'_of_not_mem_boundary K e _ j _ rfl rfl hj

Depends on / 依赖: _of_not_mem_boundary, hasHomology_sc
-/
lemma hasHomology_of_not_mem_boundary (hj : ¬ e.BoundaryGE j) :
    (K.truncGE' e).HasHomology j :=
  hasHomology_sc'_of_not_mem_boundary K e _ j _ rfl rfl hj

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `quasiIsoAt_restrictionToTruncGE'` / 引理 `quasiIsoAt_restrictionToTruncGE'`

English:
lemma quasiIsoAt_restrictionToTruncGE'
  statement: (hj : ¬ e.BoundaryGE j)
  proof: by
  rw [quasiIsoAt_iff]
  let φ := (shortComplexFunctor C c j).map (K.restrictionToTruncGE' e)
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := K.isIso_restrictionToTruncGE' e j hj
  have : IsIso φ.τ₃ := K.isIso_restrictionToTruncGE' e _ (e.not_boundaryGE_next' hj rfl)
  exa

中文:
引理 quasiIsoAt_restrictionToTruncGE'
  结论: (hj : ¬ e.BoundaryGE j)
  证明: by
  rw [quasiIsoAt_iff]
  let φ := (shortComplexFunctor C c j).map (K.restrictionToTruncGE' e)
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := K.isIso_restrictionToTruncGE' e j hj
  have : IsIso φ.τ₃ := K.isIso_restrictionToTruncGE' e _ (e.not_boundaryGE_next' hj rfl)
  exa

Depends on / 依赖: K.isIso_restrictionToTruncGE, K.restrictionToTruncGE, ShortComplex, ShortComplex.quasiIso_of_epi_of_isIso_of_mono, e.not_boundaryGE_next, infer_instance, isIso_restrictionToTruncGE, not_boundaryGE_next, quasiIsoAt_iff, quasiIso_of_epi_of_isIso_of_mono, restrictionToTruncGE, shortComplexFunctor
-/
lemma quasiIsoAt_restrictionToTruncGE' (hj : ¬ e.BoundaryGE j)
    [(K.restriction e).HasHomology j] [(K.truncGE' e).HasHomology j] :
    QuasiIsoAt (K.restrictionToTruncGE' e) j := by
  rw [quasiIsoAt_iff]
  let φ := (shortComplexFunctor C c j).map (K.restrictionToTruncGE' e)
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := K.isIso_restrictionToTruncGE' e j hj
  have : IsIso φ.τ₃ := K.isIso_restrictionToTruncGE' e _ (e.not_boundaryGE_next' hj rfl)
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

section

variable {j' : ι'} (hj' : e.f j = j') (hj : e.BoundaryGE j)

/--
lemma `homologyι_truncGE'XIsoOpcycles_inv_d` / 引理 `homologyι_truncGE'XIsoOpcycles_inv_d`

English:
lemma homologyι_truncGE'XIsoOpcycles_inv_d
  proof: by
  by_cases hjk : c.Rel j k
  · rw [K.truncGE'_d_eq_fromOpcycles e hjk hj' rfl hj, assoc, Iso.inv_hom_id_assoc,
    homologyι_comp_fromOpcycles_assoc, zero_comp]
  · rw [shape _ _ _ hjk, comp_zero]

中文:
引理 homologyι_truncGE'XIsoOpcycles_inv_d
  证明: by
  by_cases hjk : c.Rel j k
  · rw [K.truncGE'_d_eq_fromOpcycles e hjk hj' rfl hj, assoc, Iso.inv_hom_id_assoc,
    homologyι_comp_fromOpcycles_assoc, zero_comp]
  · rw [shape _ _ _ hjk, comp_zero]

Depends on / 依赖: Iso.inv_hom_id_assoc, K.truncGE, _d_eq_fromOpcycles, c.Rel, comp_zero, inv_hom_id_assoc, truncGE, zero_comp
-/
lemma homologyι_truncGE'XIsoOpcycles_inv_d :
    (K.homologyι j' ≫ (K.truncGE'XIsoOpcycles e hj' hj).inv) ≫ (K.truncGE' e).d j k = 0 := by
  by_cases hjk : c.Rel j k
  · rw [K.truncGE'_d_eq_fromOpcycles e hjk hj' rfl hj, assoc, Iso.inv_hom_id_assoc,
    homologyι_comp_fromOpcycles_assoc, zero_comp]
  · rw [shape _ _ _ hjk, comp_zero]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitKernelFork` / `isLimitKernelFork` 的定义

English:
definition isLimitKernelFork
  signature: :
  body: by
  have hk' : c'.next j' = e.f k := by simpa only [hj'] using e.next_f hk
  by_cases hjk : c.Rel j k
  · let e : parallelPair ((K.truncGE' e).d j k) 0 ≅
        parallelPair (K.fromOpcycles j' (e.f k)) 0 :=
      parallelPair.ext (K.truncGE'XIsoOpcycles e hj' hj)
        (K.truncGE'XIso e rfl (e.n

中文:
定义 isLimitKernelFork
  签名: :
  定义体: by
  have hk' : c'.next j' = e.f k := by simpa only [hj'] using e.next_f hk
  by_cases hjk : c.Rel j k
  · let e : parallelPair ((K.truncGE' e).d j k) 0 ≅
        parallelPair (K.fromOpcycles j' (e.f k)) 0 :=
      parallelPair.ext (K.truncGE'XIsoOpcycles e hj' hj)
        (K.truncGE'XIso e rfl (e.n

Depends on / 依赖: Fork.ext, IsLimit, IsLimit.ofIsoLimit, IsLimit.postcomposeHomEquiv, Iso.refl, K.fromOpcycles, K.homologyIsKernel, K.truncGE, XIsoOpcycles, _d_eq_fromOpcycles, c.Rel, e.next_f, e.not_boundaryGE_next, fromOpcycles, homologyIsKernel, next_f, not_boundaryGE_next, ofIsoLimit, parallelPair, parallelPair.ext
-/
noncomputable def isLimitKernelFork :
    IsLimit (KernelFork.ofι _ (homologyι_truncGE'XIsoOpcycles_inv_d K e j k hj' hj)) := by
  have hk' : c'.next j' = e.f k := by simpa only [hj'] using e.next_f hk
  by_cases hjk : c.Rel j k
  · let e : parallelPair ((K.truncGE' e).d j k) 0 ≅
        parallelPair (K.fromOpcycles j' (e.f k)) 0 :=
      parallelPair.ext (K.truncGE'XIsoOpcycles e hj' hj)
        (K.truncGE'XIso e rfl (e.not_boundaryGE_next hjk))
        (by simp [K.truncGE'_d_eq_fromOpcycles e hjk hj' rfl hj]) (by simp)
    exact (IsLimit.postcomposeHomEquiv e _).1
      (IsLimit.ofIsoLimit (K.homologyIsKernel _ _ hk')
      (Fork.ext (Iso.refl _) (by simp [e, Fork.ι])))
  · have := K.isIso_homologyι _ _ hk'
      (shape _ _ _ (by simpa only [← hj', e.rel_iff] using hjk))
    exact IsLimit.ofIsoLimit (KernelFork.IsLimit.ofId _ (shape _ _ _ hjk))
      (Fork.ext ((truncGE'XIsoOpcycles K e hj' hj) ≪≫ (asIso (K.homologyι j')).symm))

/--
Definition of `homologyData` / `homologyData` 的定义

English:
definition homologyData
  signature: :
  body: ShortComplex.HomologyData.ofIsLimitKernelFork _
    ((K.truncGE' e).shape _ _ (fun hij => e.not_boundaryGE_next hij hj)) _
    (isLimitKernelFork K e j k hk hj' hj)

中文:
定义 homologyData
  签名: :
  定义体: ShortComplex.HomologyData.ofIsLimitKernelFork _
    ((K.truncGE' e).shape _ _ (fun hij => e.not_boundaryGE_next hij hj)) _
    (isLimitKernelFork K e j k hk hj' hj)

Depends on / 依赖: HomologyData, K.truncGE, ShortComplex, ShortComplex.HomologyData.ofIsLimitKernelFork, e.not_boundaryGE_next, isLimitKernelFork, not_boundaryGE_next, ofIsLimitKernelFork, truncGE
-/
noncomputable def homologyData :
    ((K.truncGE' e).sc' i j k).HomologyData :=
  ShortComplex.HomologyData.ofIsLimitKernelFork _
    ((K.truncGE' e).shape _ _ (fun hij => e.not_boundaryGE_next hij hj)) _
    (isLimitKernelFork K e j k hk hj' hj)

/-- Computation of the `right.g'` field of `truncGE'.homologyData K e i j k hk hj' hj`. -/
@[simp]
/--
lemma `homologyData_right_g'` / 引理 `homologyData_right_g'`

English:
lemma homologyData_right_g'
  proof: rfl

中文:
引理 homologyData_right_g'
  证明: rfl
-/
lemma homologyData_right_g' :
    (homologyData K e i j k hk hj' hj).right.g' = (K.truncGE' e).d j k := rfl

end

/--
Instance `truncGE'_hasHomology` / 实例 `truncGE'_hasHomology`

English:
instance truncGE'_hasHomology
  signature: (i : ι)
  body: by
  by_cases hi : e.BoundaryGE i
  · exact ShortComplex.HasHomology.mk' (homologyData K e _ _ _ rfl rfl hi)
  · exact hasHomology_of_not_mem_boundary K e i hi

中文:
实例 truncGE'_hasHomology
  签名: (i : ι)
  定义体: by
  by_cases hi : e.BoundaryGE i
  · exact ShortComplex.HasHomology.mk' (homologyData K e _ _ _ rfl rfl hi)
  · exact hasHomology_of_not_mem_boundary K e i hi

Depends on / 依赖: BoundaryGE, HasHomology, ShortComplex, ShortComplex.HasHomology.mk, e.BoundaryGE, hasHomology_of_not_mem_boundary, homologyData
-/
instance truncGE'_hasHomology (i : ι) : (K.truncGE' e).HasHomology i := by
  by_cases hi : e.BoundaryGE i
  · exact ShortComplex.HasHomology.mk' (homologyData K e _ _ _ rfl rfl hi)
  · exact hasHomology_of_not_mem_boundary K e i hi

end truncGE'

variable [HasZeroObject C]

namespace truncGE

instance (i' : ι') : (K.truncGE e).HasHomology i' := by
  dsimp [truncGE]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The right homology data which allows to show that `K.πTruncGE e`
induces an isomorphism in homology in degrees `j'` such that `e.f j = j'` for some `j`. -/
@[simps]
/--
Definition of `rightHomologyMapData` / `rightHomologyMapData` 的定义

English:
definition rightHomologyMapData
  signature: {i j k : ι} {j' : ι'} (hj' : e.f j = j')
  body: (K.truncGE'XIsoOpcycles e hj' hj).inv
  φH := 𝟙 _
  commp := by
    change K.pOpcycles j' ≫ _ = _
    simp [truncGE'.homologyData, πTruncGE, e.liftExtend_f _ _ hj',
      K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e hj' hj]
  commg' := by
    have hk' : e.f k = c'.next j' := by rw [← hj'

中文:
定义 rightHomologyMapData
  签名: {i j k : ι} {j' : ι'} (hj' : e.f j = j')
  定义体: (K.truncGE'XIsoOpcycles e hj' hj).inv
  φH := 𝟙 _
  commp := by
    change K.pOpcycles j' ≫ _ = _
    simp [truncGE'.homologyData, πTruncGE, e.liftExtend_f _ _ hj',
      K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e hj' hj]
  commg' := by
    have hk' : e.f k = c'.next j' := by rw [← hj'

Depends on / 依赖: K.truncGE, XIsoOpcycles, truncGE
-/
noncomputable def rightHomologyMapData {i j k : ι} {j' : ι'} (hj' : e.f j = j')
    (hi : c.prev j = i) (hk : c.next j = k) (hj : e.BoundaryGE j) :
    ShortComplex.RightHomologyMapData ((shortComplexFunctor C c' j').map (K.πTruncGE e))
    (ShortComplex.RightHomologyData.canonical (K.sc j'))
    (extend.rightHomologyData (K.truncGE' e) e hj' hi rfl hk rfl
      (truncGE'.homologyData K e i j k hk hj' hj).right) where
  φQ := (K.truncGE'XIsoOpcycles e hj' hj).inv
  φH := 𝟙 _
  commp := by
    change K.pOpcycles j' ≫ _ = _
    simp [truncGE'.homologyData, πTruncGE, e.liftExtend_f _ _ hj',
      K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e hj' hj]
  commg' := by
    have hk' : e.f k = c'.next j' := by rw [← hj', e.next_f hk]
    dsimp
    rw [extend.rightHomologyData_g' _ _ _ _ _ _ _ _ hk']; rw [πTruncGE]; rw [e.liftExtend_f _ _ hk']; rw [truncGE'.homologyData_right_g']
    by_cases hjk : c.Rel j k
    · simp [K.truncGE'_d_eq_fromOpcycles e hjk hj' hk' hj,
        K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e hk' (e.not_boundaryGE_next hjk)]
      rfl
    · obtain rfl : k = j := by rw [← c.next_eq_self j (by simpa only [hk] using hjk), hk]
      rw [shape _ _ _ hjk]; rw [zero_comp]; rw [comp_zero]; rw [K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e hk' hj]
      simp only [restriction_X, restrictionXIso, eqToIso.inv, eqToIso.hom, assoc,
        eqToHom_trans_assoc, eqToHom_refl, id_comp]
      change 0 = K.fromOpcycles _ _ ≫ _
      rw [← cancel_epi (K.pOpcycles _)]; rw [comp_zero]; rw [p_fromOpcycles_assoc]; rw [d_pOpcycles_assoc]; rw [zero_comp]

end truncGE

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `quasiIsoAt_πTruncGE` / 引理 `quasiIsoAt_πTruncGE`

English:
lemma quasiIsoAt_πTruncGE
  given: {j : ι} {j' : ι'} (hj' : e.f j = j')
  proof: by
  rw [quasiIsoAt_iff]
  by_cases hj : e.BoundaryGE j
  · rw [(truncGE.rightHomologyMapData K e hj' rfl rfl hj).quasiIso_iff]
    dsimp
    infer_instance
  · let φ := (shortComplexFunctor C c' j').map (K.πTruncGE e)
    have : Epi φ.τ₁ := by
      by_cases hi : exists i, e.f i = c'.prev j'
      

中文:
引理 quasiIsoAt_πTruncGE
  条件: {j : ι} {j' : ι'} (hj' : e.f j = j')
  证明: by
  rw [quasiIsoAt_iff]
  by_cases hj : e.BoundaryGE j
  · rw [(truncGE.rightHomologyMapData K e hj' rfl rfl hj).quasiIso_iff]
    dsimp
    infer_instance
  · let φ := (shortComplexFunctor C c' j').map (K.πTruncGE e)
    have : Epi φ.τ₁ := by
      by_cases hi : exists i, e.f i = c'.prev j'
      

Depends on / 依赖: BoundaryGE, IsZero, IsZero.epi, e.BoundaryGE, e.epi_liftExtend_f_iff, e.isIso_liftExtend_f_iff, epi_liftExtend_f_iff, infer_instance, isIso_liftExtend_f_iff, isZero_extend_X, quasiIsoAt_iff, quasiIso_iff, rightHomologyMapData, shortComplexFunctor, truncGE, truncGE.rightHomologyMapData
-/
lemma quasiIsoAt_πTruncGE {j : ι} {j' : ι'} (hj' : e.f j = j') :
    QuasiIsoAt (K.πTruncGE e) j' := by
  rw [quasiIsoAt_iff]
  by_cases hj : e.BoundaryGE j
  · rw [(truncGE.rightHomologyMapData K e hj' rfl rfl hj).quasiIso_iff]
    dsimp
    infer_instance
  · let φ := (shortComplexFunctor C c' j').map (K.πTruncGE e)
    have : Epi φ.τ₁ := by
      by_cases hi : exists i, e.f i = c'.prev j'
      · obtain ⟨i, hi⟩ := hi
        dsimp [φ, πTruncGE]
        rw [e.epi_liftExtend_f_iff _ _ hi]
        infer_instance
      · apply IsZero.epi (isZero_extend_X _ _ _ (by simpa using hi))
    have : IsIso φ.τ₂ := by
      dsimp [φ, πTruncGE]
      rw [e.isIso_liftExtend_f_iff _ _ hj']
      exact K.isIso_restrictionToTruncGE' e j hj
    have : IsIso φ.τ₃ := by
      dsimp [φ, πTruncGE]
      have : c'.next j' = e.f (c.next j) := by simpa only [← hj'] using e.next_f rfl
      rw [e.isIso_liftExtend_f_iff _ _ this.symm]
      exact K.isIso_restrictionToTruncGE' e _ (e.not_boundaryGE_next' hj rfl)
    exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

instance (i : ι) : QuasiIsoAt (K.πTruncGE e) (e.f i) := K.quasiIsoAt_πTruncGE e rfl

/--
lemma `quasiIso_πTruncGE_iff_isSupported` / 引理 `quasiIso_πTruncGE_iff_isSupported`

English:
lemma quasiIso_πTruncGE_iff_isSupported
  proof: by
  constructor
  · intro
    refine ⟨fun i' hi' => ?_⟩
    rw [exactAt_iff_of_quasiIsoAt (K.πTruncGE e) i']
    exact (K.truncGE e).exactAt_of_isSupported e i' hi'
  · intro
    rw [quasiIso_iff]
    intro i'
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      infer_instance

中文:
引理 quasiIso_πTruncGE_iff_isSupported
  证明: by
  constructor
  · intro
    refine ⟨fun i' hi' => ?_⟩
    rw [exactAt_iff_of_quasiIsoAt (K.πTruncGE e) i']
    exact (K.truncGE e).exactAt_of_isSupported e i' hi'
  · intro
    rw [quasiIso_iff]
    intro i'
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      infer_instance

Depends on / 依赖: K.truncGE, all_goals, exactAt_iff_of_quasiIsoAt, exactAt_of_isSupported, infer_instance, quasiIsoAt_iff_exactAt, quasiIso_iff, truncGE
-/
lemma quasiIso_πTruncGE_iff_isSupported :
    QuasiIso (K.πTruncGE e) ↔ K.IsSupported e := by
  constructor
  · intro
    refine ⟨fun i' hi' => ?_⟩
    rw [exactAt_iff_of_quasiIsoAt (K.πTruncGE e) i']
    exact (K.truncGE e).exactAt_of_isSupported e i' hi'
  · intro
    rw [quasiIso_iff]
    intro i'
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      infer_instance
    · rw [quasiIsoAt_iff_exactAt (K.πTruncGE e) i']
      all_goals exact exactAt_of_isSupported _ e i' (by simpa using hi')

/--
lemma `acyclic_truncGE_iff_isSupportedOutside` / 引理 `acyclic_truncGE_iff_isSupportedOutside`

English:
lemma acyclic_truncGE_iff_isSupportedOutside
  proof: by
  constructor
  · intro hK
    exact ⟨fun i => by simpa only [exactAt_iff_of_quasiIsoAt (K.πTruncGE e)] using hK (e.f i)⟩
  · intro hK i'
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      simpa only [← exactAt_iff_of_quasiIsoAt (K.πTruncGE e)] using hK.exactAt i
    · exa

中文:
引理 acyclic_truncGE_iff_isSupportedOutside
  证明: by
  constructor
  · intro hK
    exact ⟨fun i => by simpa only [exactAt_iff_of_quasiIsoAt (K.πTruncGE e)] using hK (e.f i)⟩
  · intro hK i'
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      simpa only [← exactAt_iff_of_quasiIsoAt (K.πTruncGE e)] using hK.exactAt i
    · exa

Depends on / 依赖: exactAt, exactAt_iff_of_quasiIsoAt, exactAt_of_isSupported, hK.exactAt
-/
lemma acyclic_truncGE_iff_isSupportedOutside :
    (K.truncGE e).Acyclic ↔ K.IsSupportedOutside e := by
  constructor
  · intro hK
    exact ⟨fun i => by simpa only [exactAt_iff_of_quasiIsoAt (K.πTruncGE e)] using hK (e.f i)⟩
  · intro hK i'
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      simpa only [← exactAt_iff_of_quasiIsoAt (K.πTruncGE e)] using hK.exactAt i
    · exact exactAt_of_isSupported _ e i' (by simpa using hi')

variable {K L}

/--
lemma `Acyclic.truncGE` / 引理 `Acyclic.truncGE`

English:
lemma Acyclic.truncGE
  given: (hK : K.Acyclic) (e : c.Embedding c') [e.IsTruncGE]
  proof: by
  rw [acyclic_truncGE_iff_isSupportedOutside]
  exact ⟨fun _ => hK _⟩

中文:
引理 非循环.truncGE
  条件: (hK : K.非循环) (e : c.嵌入 c') [e.是TruncGE]
  证明: by
  rw [acyclic_truncGE_iff_isSupportedOutside]
  exact ⟨fun _ => hK _⟩

Depends on / 依赖: acyclic_truncGE_iff_isSupportedOutside
-/
lemma Acyclic.truncGE (hK : K.Acyclic) (e : c.Embedding c') [e.IsTruncGE] :
    (K.truncGE e).Acyclic := by
  rw [acyclic_truncGE_iff_isSupportedOutside]
  exact ⟨fun _ => hK _⟩

/--
lemma `quasiIso_truncGEMap_iff` / 引理 `quasiIso_truncGEMap_iff`

English:
lemma quasiIso_truncGEMap_iff
  proof: by
  have : forall (i : ι) (i' : ι') (_ : e.f i = i'),
      QuasiIsoAt (truncGEMap φ e) i' ↔ QuasiIsoAt φ i' := by
    rintro i _ rfl
    rw [← quasiIsoAt_iff_comp_left (K.πTruncGE e)]; rw [πTruncGE_naturality φ e]; rw [quasiIsoAt_iff_comp_right]
  rw [quasiIso_iff]
  constructor
  · intro h i i' h

中文:
引理 quasiIso_truncGEMap_iff
  证明: by
  have : forall (i : ι) (i' : ι') (_ : e.f i = i'),
      QuasiIsoAt (truncGEMap φ e) i' ↔ QuasiIsoAt φ i' := by
    rintro i _ rfl
    rw [← quasiIsoAt_iff_comp_left (K.πTruncGE e)]; rw [πTruncGE_naturality φ e]; rw [quasiIsoAt_iff_comp_right]
  rw [quasiIso_iff]
  constructor
  · intro h i i' h

Depends on / 依赖: QuasiIsoAt, all_goals, exactAt_of_isSupport, quasiIsoAt_iff_comp_left, quasiIsoAt_iff_comp_right, quasiIsoAt_iff_exactAt, quasiIso_iff, truncGEMap
-/
lemma quasiIso_truncGEMap_iff :
    QuasiIso (truncGEMap φ e) ↔ forall (i : ι) (i' : ι') (_ : e.f i = i'), QuasiIsoAt φ i' := by
  have : forall (i : ι) (i' : ι') (_ : e.f i = i'),
      QuasiIsoAt (truncGEMap φ e) i' ↔ QuasiIsoAt φ i' := by
    rintro i _ rfl
    rw [← quasiIsoAt_iff_comp_left (K.πTruncGE e)]; rw [πTruncGE_naturality φ e]; rw [quasiIsoAt_iff_comp_right]
  rw [quasiIso_iff]
  constructor
  · intro h i i' hi
    simpa only [← this i i' hi] using h i'
  · intro h i'
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      simpa only [this i i' hi] using h i i' hi
    · rw [quasiIsoAt_iff_exactAt]
      all_goals exact exactAt_of_isSupported _ e i' (by simpa using hi')

end HomologicalComplex
