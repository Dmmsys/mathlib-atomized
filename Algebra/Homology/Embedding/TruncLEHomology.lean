/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
public import Mathlib.Algebra.Homology.Embedding.TruncLE
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # The homology of a canonical truncation

Given an embedding of complex shapes `e : Embedding c c'`,
we relate the homology of `K : HomologicalComplex C c'` and of
`K.truncLE e : HomologicalComplex C c'`.

The main result is that `K.ιTruncLE e : K.truncLE e ⟶ K` induces a
quasi-isomorphism in degree `e.f i` for all `i`. (Note that the complex
`K.truncLE e` is exact in degrees that are not in the image of `e.f`.)

All the results are obtained by dualising the results in the file `Embedding.TruncGEHomology`.

Moreover, if `C` is an abelian category, we introduce the cokernel
sequence `K.shortComplexTruncLE e` of the monomorphism `K.ιTruncLE e`.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C]

section

variable [HasZeroMorphisms C] (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c')
  [e.IsTruncLE] [forall i', K.HasHomology i'] [forall i', L.HasHomology i']

namespace truncLE'

set_option backward.isDefEq.respectTransparency false in
/--
lemma `quasiIsoAt_truncLE'ToRestriction` / 引理 `quasiIsoAt_truncLE'ToRestriction`

English:
lemma quasiIsoAt_truncLE'ToRestriction
  statement: (j : ι) (hj : ¬ e.BoundaryLE j)
  proof: by
  dsimp only [truncLE'ToRestriction]
  have : (K.op.restriction e.op).HasHomology j :=
    inferInstanceAs ((K.restriction e).op.HasHomology j)
  rw [quasiIsoAt_unopFunctor_map_iff]
  exact truncGE'.quasiIsoAt_restrictionToTruncGE' K.op e.op j (by simpa)

中文:
引理 quasiIsoAt_truncLE'ToRestriction
  结论: (j : ι) (hj : ¬ e.BoundaryLE j)
  证明: by
  dsimp only [truncLE'ToRestriction]
  have : (K.op.restriction e.op).HasHomology j :=
    inferInstanceAs ((K.restriction e).op.HasHomology j)
  rw [quasiIsoAt_unopFunctor_map_iff]
  exact truncGE'.quasiIsoAt_restrictionToTruncGE' K.op e.op j (by simpa)

Depends on / 依赖: HasHomology, K.op, K.op.restriction, K.restriction, ToRestriction, e.op, op.HasHomology, quasiIsoAt_restrictionToTruncGE, quasiIsoAt_unopFunctor_map_iff, restriction, truncGE, truncLE
-/
lemma quasiIsoAt_truncLE'ToRestriction (j : ι) (hj : ¬ e.BoundaryLE j)
    [(K.restriction e).HasHomology j] [(K.truncLE' e).HasHomology j] :
    QuasiIsoAt (K.truncLE'ToRestriction e) j := by
  dsimp only [truncLE'ToRestriction]
  have : (K.op.restriction e.op).HasHomology j :=
    inferInstanceAs ((K.restriction e).op.HasHomology j)
  rw [quasiIsoAt_unopFunctor_map_iff]
  exact truncGE'.quasiIsoAt_restrictionToTruncGE' K.op e.op j (by simpa)

/--
Instance `truncLE'_hasHomology` / 实例 `truncLE'_hasHomology`

English:
instance truncLE'_hasHomology
  signature: (i : ι)
  body: inferInstanceAs ((K.op.truncGE' e.op).unop.HasHomology i)

中文:
实例 truncLE'_hasHomology
  签名: (i : ι)
  定义体: inferInstanceAs ((K.op.truncGE' e.op).unop.HasHomology i)

Depends on / 依赖: HasHomology, K.op.truncGE, e.op, truncGE, unop.HasHomology
-/
instance truncLE'_hasHomology (i : ι) : (K.truncLE' e).HasHomology i :=
  inferInstanceAs ((K.op.truncGE' e.op).unop.HasHomology i)

end truncLE'

variable [HasZeroObject C]

instance (i' : ι') : (K.truncLE e).HasHomology i' :=
  inferInstanceAs ((K.op.truncGE e.op).unop.HasHomology i')

/--
lemma `quasiIsoAt_ιTruncLE` / 引理 `quasiIsoAt_ιTruncLE`

English:
lemma quasiIsoAt_ιTruncLE
  given: {j : ι} {j' : ι'} (hj' : e.f j = j')
  proof: by
  have := K.op.quasiIsoAt_πTruncGE e.op hj'
  exact inferInstanceAs (QuasiIsoAt ((unopFunctor _ _).map (K.op.πTruncGE e.op).op) j')

中文:
引理 quasiIsoAt_ιTruncLE
  条件: {j : ι} {j' : ι'} (hj' : e.f j = j')
  证明: by
  have := K.op.quasiIsoAt_πTruncGE e.op hj'
  exact inferInstanceAs (QuasiIsoAt ((unopFunctor _ _).map (K.op.πTruncGE e.op).op) j')

Depends on / 依赖: K.op, K.op.quasiIsoAt_, QuasiIsoAt, e.op, unopFunctor
-/
lemma quasiIsoAt_ιTruncLE {j : ι} {j' : ι'} (hj' : e.f j = j') :
    QuasiIsoAt (K.ιTruncLE e) j' := by
  have := K.op.quasiIsoAt_πTruncGE e.op hj'
  exact inferInstanceAs (QuasiIsoAt ((unopFunctor _ _).map (K.op.πTruncGE e.op).op) j')

instance (i : ι) : QuasiIsoAt (K.ιTruncLE e) (e.f i) := K.quasiIsoAt_ιTruncLE e rfl

/--
lemma `quasiIso_ιTruncLE_iff_isSupported` / 引理 `quasiIso_ιTruncLE_iff_isSupported`

English:
lemma quasiIso_ιTruncLE_iff_isSupported
  proof: by
  rw [← quasiIso_opFunctor_map_iff]; rw [← isSupported_op_iff]
  exact K.op.quasiIso_πTruncGE_iff_isSupported e.op

中文:
引理 quasiIso_ιTruncLE_iff_isSupported
  证明: by
  rw [← quasiIso_opFunctor_map_iff]; rw [← isSupported_op_iff]
  exact K.op.quasiIso_πTruncGE_iff_isSupported e.op

Depends on / 依赖: K.op.quasiIso_, e.op, isSupported_op_iff, quasiIso_opFunctor_map_iff
-/
lemma quasiIso_ιTruncLE_iff_isSupported :
    QuasiIso (K.ιTruncLE e) ↔ K.IsSupported e := by
  rw [← quasiIso_opFunctor_map_iff]; rw [← isSupported_op_iff]
  exact K.op.quasiIso_πTruncGE_iff_isSupported e.op

/--
lemma `acyclic_truncLE_iff_isSupportedOutside` / 引理 `acyclic_truncLE_iff_isSupportedOutside`

English:
lemma acyclic_truncLE_iff_isSupportedOutside
  proof: by
  rw [← acyclic_op_iff]; rw [← isSupportedOutside_op_iff]
  exact K.op.acyclic_truncGE_iff_isSupportedOutside e.op

中文:
引理 acyclic_truncLE_iff_isSupportedOutside
  证明: by
  rw [← acyclic_op_iff]; rw [← isSupportedOutside_op_iff]
  exact K.op.acyclic_truncGE_iff_isSupportedOutside e.op

Depends on / 依赖: K.op.acyclic_truncGE_iff_isSupportedOutside, acyclic_op_iff, acyclic_truncGE_iff_isSupportedOutside, e.op, isSupportedOutside_op_iff
-/
lemma acyclic_truncLE_iff_isSupportedOutside :
    (K.truncLE e).Acyclic ↔ K.IsSupportedOutside e := by
  rw [← acyclic_op_iff]; rw [← isSupportedOutside_op_iff]
  exact K.op.acyclic_truncGE_iff_isSupportedOutside e.op

variable {K L}

/--
lemma `Acyclic.truncLE` / 引理 `Acyclic.truncLE`

English:
lemma Acyclic.truncLE
  given: (hK : K.Acyclic) (e : c.Embedding c') [e.IsTruncLE]
  proof: by
  rw [acyclic_truncLE_iff_isSupportedOutside]
  exact ⟨fun _ => hK _⟩

中文:
引理 非循环.truncLE
  条件: (hK : K.非循环) (e : c.嵌入 c') [e.是TruncLE]
  证明: by
  rw [acyclic_truncLE_iff_isSupportedOutside]
  exact ⟨fun _ => hK _⟩

Depends on / 依赖: acyclic_truncLE_iff_isSupportedOutside
-/
lemma Acyclic.truncLE (hK : K.Acyclic) (e : c.Embedding c') [e.IsTruncLE] :
    (K.truncLE e).Acyclic := by
  rw [acyclic_truncLE_iff_isSupportedOutside]
  exact ⟨fun _ => hK _⟩

/--
lemma `quasiIso_truncLEMap_iff` / 引理 `quasiIso_truncLEMap_iff`

English:
lemma quasiIso_truncLEMap_iff
  proof: by
  rw [← quasiIso_opFunctor_map_iff]
  simp only [← quasiIsoAt_opFunctor_map_iff φ]
  apply quasiIso_truncGEMap_iff

中文:
引理 quasiIso_truncLEMap_iff
  证明: by
  rw [← quasiIso_opFunctor_map_iff]
  simp only [← quasiIsoAt_opFunctor_map_iff φ]
  apply quasiIso_truncGEMap_iff

Depends on / 依赖: quasiIsoAt_opFunctor_map_iff, quasiIso_opFunctor_map_iff, quasiIso_truncGEMap_iff
-/
lemma quasiIso_truncLEMap_iff :
    QuasiIso (truncLEMap φ e) ↔ forall (i : ι) (i' : ι') (_ : e.f i = i'), QuasiIsoAt φ i' := by
  rw [← quasiIso_opFunctor_map_iff]
  simp only [← quasiIsoAt_opFunctor_map_iff φ]
  apply quasiIso_truncGEMap_iff

end

section

variable [Abelian C] (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]

/-- The cokernel sequence of the monomorphism `K.ιTruncLE e`. -/
@[simps X₁ X₂ f]
/--
Definition of `shortComplexTruncLE` / `shortComplexTruncLE` 的定义

English:
definition shortComplexTruncLE
  signature: : ShortComplex (HomologicalComplex C c')
  body: ShortComplex.mk (K.ιTruncLE e) _ (cokernel.condition _)

中文:
定义 shortComplexTruncLE
  签名: : 短复形 (同调复形 C c')
  定义体: ShortComplex.mk (K.ιTruncLE e) _ (cokernel.condition _)

Depends on / 依赖: ShortComplex, ShortComplex.mk, cokernel, cokernel.condition, condition
-/
noncomputable def shortComplexTruncLE : ShortComplex (HomologicalComplex C c') :=
  ShortComplex.mk (K.ιTruncLE e) _ (cokernel.condition _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (K.shortComplexTruncLE e).f
  body: by
  dsimp [shortComplexTruncLE]
  infer_instance

中文:
实例 :
  签名: 单态射 (K.shortComplexTruncLE e).f
  定义体: by
  dsimp [shortComplexTruncLE]
  infer_instance

Depends on / 依赖: infer_instance, shortComplexTruncLE
-/
instance : Mono (K.shortComplexTruncLE e).f := by
  dsimp [shortComplexTruncLE]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (K.shortComplexTruncLE e).g
  body: by
  dsimp [shortComplexTruncLE]
  infer_instance

中文:
实例 :
  签名: 满态射 (K.shortComplexTruncLE e).g
  定义体: by
  dsimp [shortComplexTruncLE]
  infer_instance

Depends on / 依赖: infer_instance, shortComplexTruncLE
-/
instance : Epi (K.shortComplexTruncLE e).g := by
  dsimp [shortComplexTruncLE]
  infer_instance

/--
lemma `shortComplexTruncLE_shortExact` / 引理 `shortComplexTruncLE_shortExact`

English:
lemma shortComplexTruncLE_shortExact
  proof: ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

中文:
引理 shortComplexTruncLE_shortExact
  证明: ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

Depends on / 依赖: ShortComplex, ShortComplex.exact_of_g_is_cokernel, cokernelIsCokernel, exact_of_g_is_cokernel
-/
lemma shortComplexTruncLE_shortExact :
    (K.shortComplexTruncLE e).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

/--
lemma `mono_homologyMap_shortComplexTruncLE_g` / 引理 `mono_homologyMap_shortComplexTruncLE_g`

English:
lemma mono_homologyMap_shortComplexTruncLE_g
  given: (i' : ι') (hi' : forall i, e.f i != i')
  proof: ((K.shortComplexTruncLE_shortExact e).homology_exact₂ i').mono_g
    (by apply ((K.truncLE e).exactAt_of_isSupported e i' hi').isZero_homology.eq_of_src)

中文:
引理 mono_homologyMap_shortComplexTruncLE_g
  条件: (i' : ι') (hi' : 对任意 i, e.f i != i')
  证明: ((K.shortComplexTruncLE_shortExact e).homology_exact₂ i').mono_g
    (by apply ((K.truncLE e).exactAt_of_isSupported e i' hi').isZero_homology.eq_of_src)

Depends on / 依赖: K.shortComplexTruncLE_shortExact, K.truncLE, eq_of_src, exactAt_of_isSupported, isZero_homology, isZero_homology.eq_of_src, mono_g, shortComplexTruncLE_shortExact, truncLE
-/
lemma mono_homologyMap_shortComplexTruncLE_g (i' : ι') (hi' : forall i, e.f i != i') :
    Mono (homologyMap (K.shortComplexTruncLE e).g i') :=
  ((K.shortComplexTruncLE_shortExact e).homology_exact₂ i').mono_g
    (by apply ((K.truncLE e).exactAt_of_isSupported e i' hi').isZero_homology.eq_of_src)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `shortComplexTruncLE_shortExact_δ_eq_zero` / 引理 `shortComplexTruncLE_shortExact_δ_eq_zero`

English:
lemma shortComplexTruncLE_shortExact_δ_eq_zero
  given: (i' j' : ι') (hij' : c'.Rel i' j')
  proof: by
  by_cases hj : exists j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    rw [← cancel_mono (homologyMap (K.ιTruncLE e) (e.f j))]; rw [zero_comp]
    exact (K.shortComplexTruncLE_shortExact e).δ_comp i' _ hij'
  · apply ((K.truncLE e).exactAt_of_isSupported e j'
      (by simpa using hj)).isZero_homolog

中文:
引理 shortComplexTruncLE_shortExact_δ_eq_zero
  条件: (i' j' : ι') (hij' : c'.关系 i' j')
  证明: by
  by_cases hj : exists j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    rw [← cancel_mono (homologyMap (K.ιTruncLE e) (e.f j))]; rw [zero_comp]
    exact (K.shortComplexTruncLE_shortExact e).δ_comp i' _ hij'
  · apply ((K.truncLE e).exactAt_of_isSupported e j'
      (by simpa using hj)).isZero_homolog

Depends on / 依赖: K.shortComplexTruncLE_shortExact, K.truncLE, cancel_mono, eq_of_tgt, exactAt_of_isSupported, homologyMap, isZero_homology, isZero_homology.eq_of_tgt, shortComplexTruncLE_shortExact, truncLE, zero_comp
-/
lemma shortComplexTruncLE_shortExact_δ_eq_zero (i' j' : ι') (hij' : c'.Rel i' j') :
    (K.shortComplexTruncLE_shortExact e).δ i' j' hij' = 0 := by
  by_cases hj : exists j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    rw [← cancel_mono (homologyMap (K.ιTruncLE e) (e.f j))]; rw [zero_comp]
    exact (K.shortComplexTruncLE_shortExact e).δ_comp i' _ hij'
  · apply ((K.truncLE e).exactAt_of_isSupported e j'
      (by simpa using hj)).isZero_homology.eq_of_tgt

/--
Instance `epi_homologyMap_shortComplexTruncLE_g` / 实例 `epi_homologyMap_shortComplexTruncLE_g`

English:
instance epi_homologyMap_shortComplexTruncLE_g
  signature: (i' : ι')
  body: by
  by_cases hi' : exists j', c'.Rel i' j'
  · obtain ⟨j', hj'⟩ := hi'
    exact ((K.shortComplexTruncLE_shortExact e).homology_exact₃ i' j' hj').epi_f (by simp)
  · exact epi_homologyMap_of_epi_of_not_rel _ _ (by simpa using hi')

中文:
实例 epi_homologyMap_shortComplexTruncLE_g
  签名: (i' : ι')
  定义体: by
  by_cases hi' : exists j', c'.Rel i' j'
  · obtain ⟨j', hj'⟩ := hi'
    exact ((K.shortComplexTruncLE_shortExact e).homology_exact₃ i' j' hj').epi_f (by simp)
  · exact epi_homologyMap_of_epi_of_not_rel _ _ (by simpa using hi')

Depends on / 依赖: K.shortComplexTruncLE_shortExact, epi_f, epi_homologyMap_of_epi_of_not_rel, shortComplexTruncLE_shortExact
-/
instance epi_homologyMap_shortComplexTruncLE_g (i' : ι') :
    Epi (homologyMap (K.shortComplexTruncLE e).g i') := by
  by_cases hi' : exists j', c'.Rel i' j'
  · obtain ⟨j', hj'⟩ := hi'
    exact ((K.shortComplexTruncLE_shortExact e).homology_exact₃ i' j' hj').epi_f (by simp)
  · exact epi_homologyMap_of_epi_of_not_rel _ _ (by simpa using hi')

/--
lemma `isIso_homologyMap_shortComplexTruncLE_g` / 引理 `isIso_homologyMap_shortComplexTruncLE_g`

English:
lemma isIso_homologyMap_shortComplexTruncLE_g
  given: (i' : ι') (hi' : forall i, e.f i != i')
  proof: by
  have := K.mono_homologyMap_shortComplexTruncLE_g e i' hi'
  apply isIso_of_mono_of_epi

中文:
引理 isIso_homologyMap_shortComplexTruncLE_g
  条件: (i' : ι') (hi' : 对任意 i, e.f i != i')
  证明: by
  have := K.mono_homologyMap_shortComplexTruncLE_g e i' hi'
  apply isIso_of_mono_of_epi

Depends on / 依赖: K.mono_homologyMap_shortComplexTruncLE_g, isIso_of_mono_of_epi, mono_homologyMap_shortComplexTruncLE_g
-/
lemma isIso_homologyMap_shortComplexTruncLE_g (i' : ι') (hi' : forall i, e.f i != i') :
    IsIso (homologyMap (K.shortComplexTruncLE e).g i') := by
  have := K.mono_homologyMap_shortComplexTruncLE_g e i' hi'
  apply isIso_of_mono_of_epi

/--
lemma `quasiIsoAt_shortComplexTruncLE_g` / 引理 `quasiIsoAt_shortComplexTruncLE_g`

English:
lemma quasiIsoAt_shortComplexTruncLE_g
  given: (i' : ι') (hi' : forall i, e.f i != i')
  proof: by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact K.isIso_homologyMap_shortComplexTruncLE_g e i' hi'

中文:
引理 quasiIsoAt_shortComplexTruncLE_g
  条件: (i' : ι') (hi' : 对任意 i, e.f i != i')
  证明: by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact K.isIso_homologyMap_shortComplexTruncLE_g e i' hi'

Depends on / 依赖: K.isIso_homologyMap_shortComplexTruncLE_g, isIso_homologyMap_shortComplexTruncLE_g, quasiIsoAt_iff_isIso_homologyMap
-/
lemma quasiIsoAt_shortComplexTruncLE_g (i' : ι') (hi' : forall i, e.f i != i') :
    QuasiIsoAt (K.shortComplexTruncLE e).g i' := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact K.isIso_homologyMap_shortComplexTruncLE_g e i' hi'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `shortComplexTruncLE_X₃_isSupportedOutside` / 引理 `shortComplexTruncLE_X₃_isSupportedOutside`

English:
lemma shortComplexTruncLE_X₃_isSupportedOutside
  proof: by
    rw [exactAt_iff_isZero_homology]
    by_cases hi : exists j', c'.Rel (e.f i) j'
    · obtain ⟨j', hj'⟩ := hi
      apply ((K.shortComplexTruncLE_shortExact e).homology_exact₃ (e.f i) j' hj').isZero_X₂
      · rw [← cancel_epi (homologyMap (K.ιTruncLE e) (e.f i)), comp_zero]
        dsimp [sho

中文:
引理 shortComplexTruncLE_X₃_isSupportedOutside
  证明: by
    rw [exactAt_iff_isZero_homology]
    by_cases hi : exists j', c'.Rel (e.f i) j'
    · obtain ⟨j', hj'⟩ := hi
      apply ((K.shortComplexTruncLE_shortExact e).homology_exact₃ (e.f i) j' hj').isZero_X₂
      · rw [← cancel_epi (homologyMap (K.ιTruncLE e) (e.f i)), comp_zero]
        dsimp [sho

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, K.shortComplexTruncLE, K.shortComplexTruncLE_shortExact, cancel_e, cancel_epi, cokernel, cokernel.condition, comp_zero, condition, exactAt_iff_isZero_homology, homologyMap, homologyMap_comp, homologyMap_zero, iff_id_eq_zero, infer_instance, shortComplexTruncLE, shortComplexTruncLE_shortExact
-/
lemma shortComplexTruncLE_X₃_isSupportedOutside :
    (K.shortComplexTruncLE e).X₃.IsSupportedOutside e where
  exactAt i := by
    rw [exactAt_iff_isZero_homology]
    by_cases hi : exists j', c'.Rel (e.f i) j'
    · obtain ⟨j', hj'⟩ := hi
      apply ((K.shortComplexTruncLE_shortExact e).homology_exact₃ (e.f i) j' hj').isZero_X₂
      · rw [← cancel_epi (homologyMap (K.ιTruncLE e) (e.f i)), comp_zero]
        dsimp [shortComplexTruncLE]
        rw [← homologyMap_comp]; rw [cokernel.condition]; rw [homologyMap_zero]
      · simp
    · have : IsIso (homologyMap (K.shortComplexTruncLE e).f (e.f i)) := by dsimp; infer_instance
      rw [IsZero.iff_id_eq_zero]; rw [← cancel_epi (homologyMap (K.shortComplexTruncLE e).g (e.f i))]; rw [comp_id]; rw [comp_zero]; rw [← cancel_epi (homologyMap (K.shortComplexTruncLE e).f (e.f i))]; rw [comp_zero]; rw [← homologyMap_comp]; rw [ShortComplex.zero]; rw [homologyMap_zero]

end

end HomologicalComplex
