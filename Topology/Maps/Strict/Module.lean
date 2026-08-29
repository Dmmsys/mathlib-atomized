/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Maps.Strict.Group

/-!
# Strict linear maps

In this file, we study continuous linear maps which are *strict* in the sense of
`Topology.IsStrictMap`. So far, all the results in this file are direct
adaptations from the theory of strict homomorphisms of topological additive groups.
-/

@[expose] public section

open Topology

namespace LinearMap

variable {R S M N Nₗ M' Nₗ' : Type*} [Ring R] [Ring S] {σ : R ->+* S}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup Nₗ] [AddCommGroup M'] [AddCommGroup Nₗ']
  [Module R M] [Module S N] [Module R Nₗ] [Module R M'] [Module R Nₗ']
  {f : M ->ₛₗ[σ] N} {fₗ : M ->ₗ[R] Nₗ} {gₗ : M' ->ₗ[R] Nₗ'}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Nₗ]

/--
lemma `isStrictMap_iff_isEmbedding_liftQ_ker` / 引理 `isStrictMap_iff_isEmbedding_liftQ_ker`

English:
lemma isStrictMap_iff_isEmbedding_liftQ_ker
  proof: f.toAddMonoidHom.isStrictMap_iff_isEmbedding_kerLift

中文:
引理 isStrictMap_iff_isEmbedding_liftQ_ker
  证明: f.toAddMonoidHom.isStrictMap_iff_isEmbedding_kerLift
-/
protected lemma isStrictMap_iff_isEmbedding_liftQ_ker :
    IsStrictMap f ↔ IsEmbedding (f.ker.liftQ f le_rfl) :=
  f.toAddMonoidHom.isStrictMap_iff_isEmbedding_kerLift

/--
lemma `isStrictMap_iff_isHomeomorph_quotKerEquivRange` / 引理 `isStrictMap_iff_isHomeomorph_quotKerEquivRange`

English:
lemma isStrictMap_iff_isHomeomorph_quotKerEquivRange
  proof: by
  -- Note: right now, this cannot easily be deduced from the `AddMonoidHom` statement, because
  -- `fₗ.quotKerEquivRange.toAddEquiv` is not def-eq to
  -- `QuotientAddGroup.quotientKerEquivRange fₗ.toAddMonoidHom`. This would require
  -- fixing the definition of `LinearMap.quotKerEquivRange`.
  simp_rw [isHomeomorph_iff_isStrictMap_bijective, EquivLike.bijective, and_true,
    fₗ.ker.isQuotientMap_mkQ.isStrictMap_iff, IsEmbedding.subtypeVal.isStrictMap_iff]
  rfl

中文:
引理 isStrictMap_iff_isHomeomorph_quotKerEquivRange
  证明: by
  -- Note: right now, this cannot easily be deduced from the `AddMonoidHom` statement, because
  -- `fₗ.quotKerEquivRange.toAddEquiv` is not def-eq to
  -- `QuotientAddGroup.quotientKerEquivRange fₗ.toAddMonoidHom`. This would require
  -- fixing the definition of `LinearMap.quotKerEquivRange`.
  simp_rw [isHomeomorph_iff_isStrictMap_bijective, EquivLike.bijective, and_true,
    fₗ.ker.isQuotientMap_mkQ.isStrictMap_iff, IsEmbedding.subtypeVal.isStrictMap_iff]
  rfl
-/
protected lemma isStrictMap_iff_isHomeomorph_quotKerEquivRange :
    IsStrictMap fₗ ↔ IsHomeomorph fₗ.quotKerEquivRange := by
  -- Note: right now, this cannot easily be deduced from the `AddMonoidHom` statement, because
  -- `fₗ.quotKerEquivRange.toAddEquiv` is not def-eq to
  -- `QuotientAddGroup.quotientKerEquivRange fₗ.toAddMonoidHom`. This would require
  -- fixing the definition of `LinearMap.quotKerEquivRange`.
  simp_rw [isHomeomorph_iff_isStrictMap_bijective, EquivLike.bijective, and_true,
    fₗ.ker.isQuotientMap_mkQ.isStrictMap_iff, IsEmbedding.subtypeVal.isStrictMap_iff]
  rfl

/--
Definition of `_root_.ContinuousLinearEquiv.quotKerEquivRange` / `_root_.ContinuousLinearEquiv.quotKerEquivRange` 的定义

English:
definition _root_.ContinuousLinearEquiv.quotKerEquivRange
  body: .ofIsHomeomorph fₗ.quotKerEquivRange (fₗ.isStrictMap_iff_isHomeomorph_quotKerEquivRange.mp hf)

中文:
定义 _root_.连续线性等价.quotKerEquivRange
  定义体: .ofIsHomeomorph fₗ.quotKerEquivRange (fₗ.isStrictMap_iff_isHomeomorph_quotKerEquivRange.mp hf)

Depends on / 依赖: isStrictMap_iff_isHomeomorph_quotKerEquivRange, isStrictMap_iff_isHomeomorph_quotKerEquivRange.mp, ofIsHomeomorph, quotKerEquivRange
-/
noncomputable def _root_.ContinuousLinearEquiv.quotKerEquivRange
    (hf : IsStrictMap fₗ) : (M ⧸ fₗ.ker) ≃L[R] fₗ.range :=
  .ofIsHomeomorph fₗ.quotKerEquivRange (fₗ.isStrictMap_iff_isHomeomorph_quotKerEquivRange.mp hf)

variable [IsTopologicalAddGroup M]

/--
lemma `isStrictMap_iff_isOpenQuotientMap_rangeRestrict` / 引理 `isStrictMap_iff_isOpenQuotientMap_rangeRestrict`

English:
lemma isStrictMap_iff_isOpenQuotientMap_rangeRestrict
  given: [RingHomSurjective σ]
  proof: f.toAddMonoidHom.isStrictMap_iff_isOpenQuotientMap_rangeRestrict

中文:
引理 isStrictMap_iff_isOpenQuotientMap_rangeRestrict
  条件: [RingHomSurjective σ]
  证明: f.toAddMonoidHom.isStrictMap_iff_isOpenQuotientMap_rangeRestrict
-/
protected lemma isStrictMap_iff_isOpenQuotientMap_rangeRestrict [RingHomSurjective σ] :
    IsStrictMap f ↔ IsOpenQuotientMap f.rangeRestrict :=
  f.toAddMonoidHom.isStrictMap_iff_isOpenQuotientMap_rangeRestrict

variable [TopologicalSpace M'] [IsTopologicalAddGroup M'] [TopologicalSpace Nₗ']

/--
lemma `isStrictMap_prodMap_iff` / 引理 `isStrictMap_prodMap_iff`

English:
lemma isStrictMap_prodMap_iff
  proof: AddMonoidHom.isStrictMap_prodMap_iff (f := fₗ.toAddMonoidHom) (g := gₗ.toAddMonoidHom)

中文:
引理 isStrictMap_prodMap_iff
  证明: AddMonoidHom.isStrictMap_prodMap_iff (f := fₗ.toAddMonoidHom) (g := gₗ.toAddMonoidHom)
-/
protected lemma isStrictMap_prodMap_iff :
    IsStrictMap (fₗ.prodMap gₗ) ↔ IsStrictMap fₗ ∧ IsStrictMap gₗ :=
  AddMonoidHom.isStrictMap_prodMap_iff (f := fₗ.toAddMonoidHom) (g := gₗ.toAddMonoidHom)

/--
lemma `isStrictMap_prodMap` / 引理 `isStrictMap_prodMap`

English:
lemma isStrictMap_prodMap
  statement: (hf : IsStrictMap fₗ)
  proof: LinearMap.isStrictMap_prodMap_iff.mpr ⟨hf, hg⟩

中文:
引理 isStrictMap_prodMap
  结论: (hf : IsStrictMap fₗ)
  证明: LinearMap.isStrictMap_prodMap_iff.mpr ⟨hf, hg⟩
-/
protected lemma isStrictMap_prodMap (hf : IsStrictMap fₗ)
    (hg : IsStrictMap gₗ) : IsStrictMap (fₗ.prodMap gₗ) :=
  LinearMap.isStrictMap_prodMap_iff.mpr ⟨hf, hg⟩

end LinearMap
