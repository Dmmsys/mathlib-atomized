/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Algebra.Algebra.Subalgebra.IsSimpleOrder
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.SplittingField.IsSplittingField
public import Mathlib.RingTheory.Adjoin.Dimension
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.SetTheory.Cardinal.Subfield

/-!
# Adjoining Elements to Fields

This file contains many results about adjoining elements to fields.
-/

@[expose] public section

open Module Polynomial

namespace IntermediateField

section

/--
lemma `restrictScalars_le_iff` / 引理 `restrictScalars_le_iff`

English:
lemma restrictScalars_le_iff
  statement: (K : Type*) {L E : Type*} [Field K] [Field L]
  proof: .rfl

中文:
引理 restrictScalars_le_iff
  结论: (K : 类型) {L E : 类型} [Field K] [Field L]
  证明: .rfl
-/
lemma restrictScalars_le_iff (K : Type*) {L E : Type*} [Field K] [Field L]
    [Field E] [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    {E₁ E₂ : IntermediateField L E} : E₁.restrictScalars K <= E₂.restrictScalars K ↔ E₁ <= E₂ := .rfl

/--
lemma `FG.of_restrictScalars` / 引理 `FG.of_restrictScalars`

English:
lemma FG.of_restrictScalars
  statement: {K L E : Type*} [Field K] [Field L] [Field E]
  proof: by
  obtain ⟨s, hs⟩ := H
  refine ⟨s, le_antisymm ?_ ?_⟩
  · rw [adjoin_le_iff]
    exact (subset_adjoin K _).trans_eq congr(($hs : Set E))
  · rw [← restrictScalars_le_iff K, ← hs, adjoin_le_iff]
    exact subset_adjoin L _

中文:
引理 FG.of_restrictScalars
  结论: {K L E : 类型} [Field K] [Field L] [Field E]
  证明: by
  obtain ⟨s, hs⟩ := H
  refine ⟨s, le_antisymm ?_ ?_⟩
  · rw [adjoin_le_iff]
    exact (subset_adjoin K _).trans_eq congr(($hs : Set E))
  · rw [← restrictScalars_le_iff K, ← hs, adjoin_le_iff]
    exact subset_adjoin L _

Depends on / 依赖: adjoin_le_iff, le_antisymm, restrictScalars_le_iff, subset_adjoin, trans_eq
-/
lemma FG.of_restrictScalars {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    {E' : IntermediateField L E} (H : (E'.restrictScalars K).FG) : E'.FG := by
  obtain ⟨s, hs⟩ := H
  refine ⟨s, le_antisymm ?_ ?_⟩
  · rw [adjoin_le_iff]
    exact (subset_adjoin K _).trans_eq congr(($hs : Set E))
  · rw [← restrictScalars_le_iff K, ← hs, adjoin_le_iff]
    exact subset_adjoin L _

end

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {S : Set E}

/--
theorem `mem_adjoin_range_iff` / 定理 `mem_adjoin_range_iff`

English:
theorem mem_adjoin_range_iff
  given: {ι : Type*} (i : ι -> E) (x : E)
  proof: by
  simp_rw [mem_adjoin_iff_div, Algebra.adjoin_range_eq_range_aeval,
    AlgHom.mem_range, exists_exists_eq_and]

中文:
定理 mem_adjoin_range_iff
  条件: {ι : 类型} (i : ι -> E) (x : E)
  证明: by
  simp_rw [mem_adjoin_iff_div, Algebra.adjoin_range_eq_range_aeval,
    AlgHom.mem_range, exists_exists_eq_and]

Depends on / 依赖: AlgHom, AlgHom.mem_range, Algebra, Algebra.adjoin_range_eq_range_aeval, adjoin_range_eq_range_aeval, exists_exists_eq_and, mem_adjoin_iff_div, mem_range, simp_rw
-/
theorem mem_adjoin_range_iff {ι : Type*} (i : ι -> E) (x : E) :
    x in adjoin F (Set.range i) ↔ exists r s : MvPolynomial ι F,
      x = MvPolynomial.aeval i r / MvPolynomial.aeval i s := by
  simp_rw [mem_adjoin_iff_div, Algebra.adjoin_range_eq_range_aeval,
    AlgHom.mem_range, exists_exists_eq_and]

/--
theorem `mem_adjoin_iff` / 定理 `mem_adjoin_iff`

English:
theorem mem_adjoin_iff
  given: (x : E)
  proof: by
  rw [← mem_adjoin_range_iff]; rw [Subtype.range_coe]

中文:
定理 mem_adjoin_iff
  条件: (x : E)
  证明: by
  rw [← mem_adjoin_range_iff]; rw [Subtype.range_coe]

Depends on / 依赖: Subtype, Subtype.range_coe, mem_adjoin_range_iff, range_coe
-/
theorem mem_adjoin_iff (x : E) :
    x in adjoin F S ↔ exists r s : MvPolynomial S F,
      x = MvPolynomial.aeval Subtype.val r / MvPolynomial.aeval Subtype.val s := by
  rw [← mem_adjoin_range_iff]; rw [Subtype.range_coe]

/--
theorem `mem_adjoin_simple_iff` / 定理 `mem_adjoin_simple_iff`

English:
theorem mem_adjoin_simple_iff
  given: {α : E} (x : E)
  proof: by
  simp only [mem_adjoin_iff_div, Algebra.adjoin_singleton_eq_range_aeval,
    AlgHom.mem_range, exists_exists_eq_and]

中文:
定理 mem_adjoin_simple_iff
  条件: {α : E} (x : E)
  证明: by
  simp only [mem_adjoin_iff_div, Algebra.adjoin_singleton_eq_range_aeval,
    AlgHom.mem_range, exists_exists_eq_and]

Depends on / 依赖: AlgHom, AlgHom.mem_range, Algebra, Algebra.adjoin_singleton_eq_range_aeval, adjoin_singleton_eq_range_aeval, exists_exists_eq_and, mem_adjoin_iff_div, mem_range
-/
theorem mem_adjoin_simple_iff {α : E} (x : E) :
    x in adjoin F {α} ↔ exists r s : F[X], x = aeval α r / aeval α s := by
  simp only [mem_adjoin_iff_div, Algebra.adjoin_singleton_eq_range_aeval,
    AlgHom.mem_range, exists_exists_eq_and]

/--
theorem `forall_mem_adjoin_smul_eq_self_iff` / 定理 `forall_mem_adjoin_smul_eq_self_iff`

English:
theorem forall_mem_adjoin_smul_eq_self_iff
  statement: {M : Type*} [Monoid M] [MulSemiringAction M E]
  proof: by
  simpa [-adjoin_le_iff, Set.subset_def, SetLike.le_def, FixedBy.intermediateField_mem_iff] using
    adjoin_le_iff (T := FixedBy.intermediateField F E m)

中文:
定理 forall_mem_adjoin_smul_eq_self_iff
  结论: {M : 类型} [Monoid M] [MulSemiringAction M E]
  证明: by
  simpa [-adjoin_le_iff, Set.subset_def, SetLike.le_def, FixedBy.intermediateField_mem_iff] using
    adjoin_le_iff (T := FixedBy.intermediateField F E m)

Depends on / 依赖: FixedBy, FixedBy.intermediateField, FixedBy.intermediateField_mem_iff, Set.subset_def, SetLike, SetLike.le_def, adjoin_le_iff, intermediateField, intermediateField_mem_iff, le_def, subset_def
-/
theorem forall_mem_adjoin_smul_eq_self_iff {M : Type*} [Monoid M] [MulSemiringAction M E]
    [SMulCommClass M F E] (m : M) :
    (forall x in adjoin F S, m • x = x) ↔ forall x in S, m • x = x := by
  simpa [-adjoin_le_iff, Set.subset_def, SetLike.le_def, FixedBy.intermediateField_mem_iff] using
    adjoin_le_iff (T := FixedBy.intermediateField F E m)

variable {F}

section Supremum

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)

/--
Instance `finiteDimensional_sup` / 实例 `finiteDimensional_sup`

English:
instance finiteDimensional_sup
  signature: [FiniteDimensional K E1] [FiniteDimensional K E2]
  body: by
  let g := Algebra.TensorProduct.productMap E1.val E2.val
  suffices g.range = (E1 ⊔ E2).toSubalgebra by
    have h : FiniteDimensional K (Subalgebra.toSubmodule g.range) :=
      g.toLinearMap.finiteDimensional_range
    rwa [this] at h
  rw [Algebra.TensorProduct.productMap_range]; rw [E1.range

中文:
实例 finiteDimensional_sup
  签名: [FiniteDimensional K E1] [FiniteDimensional K E2]
  定义体: by
  let g := Algebra.TensorProduct.productMap E1.val E2.val
  suffices g.range = (E1 ⊔ E2).toSubalgebra by
    have h : FiniteDimensional K (Subalgebra.toSubmodule g.range) :=
      g.toLinearMap.finiteDimensional_range
    rwa [this] at h
  rw [Algebra.TensorProduct.productMap_range]; rw [E1.range

Depends on / 依赖: Algebra, Algebra.TensorProduct.productMap, Algebra.TensorProduct.productMap_range, E1.range_val, E1.val, E2.range_val, E2.val, FiniteDimensional, Subalgebra, Subalgebra.toSubmodule, TensorProduct, finiteDimensional_range, g.range, g.toLinearMap.finiteDimensional_range, productMap, productMap_range, range_val, sup_toSubalgebra_of_left, toLinearMap, toSubalgebra
-/
instance finiteDimensional_sup [FiniteDimensional K E1] [FiniteDimensional K E2] :
    FiniteDimensional K (E1 ⊔ E2 : IntermediateField K L) := by
  let g := Algebra.TensorProduct.productMap E1.val E2.val
  suffices g.range = (E1 ⊔ E2).toSubalgebra by
    have h : FiniteDimensional K (Subalgebra.toSubmodule g.range) :=
      g.toLinearMap.finiteDimensional_range
    rwa [this] at h
  rw [Algebra.TensorProduct.productMap_range]; rw [E1.range_val]; rw [E2.range_val]; rw [sup_toSubalgebra_of_left]

/--
theorem `rank_sup_le_of_isAlgebraic` / 定理 `rank_sup_le_of_isAlgebraic`

English:
theorem rank_sup_le_of_isAlgebraic
  proof: by
  have := E1.toSubalgebra.rank_sup_le_of_free E2.toSubalgebra
  rwa [← sup_toSubalgebra_of_isAlgebraic E1 E2 halg] at this

中文:
定理 rank_sup_le_of_isAlgebraic
  证明: by
  have := E1.toSubalgebra.rank_sup_le_of_free E2.toSubalgebra
  rwa [← sup_toSubalgebra_of_isAlgebraic E1 E2 halg] at this

Depends on / 依赖: E1.toSubalgebra.rank_sup_le_of_free, E2.toSubalgebra, rank_sup_le_of_free, sup_toSubalgebra_of_isAlgebraic, toSubalgebra
-/
theorem rank_sup_le_of_isAlgebraic
    (halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAlgebraic K E2) :
    Module.rank K ↥(E1 ⊔ E2) <= Module.rank K E1 * Module.rank K E2 := by
  have := E1.toSubalgebra.rank_sup_le_of_free E2.toSubalgebra
  rwa [← sup_toSubalgebra_of_isAlgebraic E1 E2 halg] at this

/--
theorem `finrank_sup_le` / 定理 `finrank_sup_le`

English:
theorem finrank_sup_le
  proof: by
  by_cases h : FiniteDimensional K E1
  · have := E1.toSubalgebra.finrank_sup_le_of_free E2.toSubalgebra
    change _ <= finrank K E1 * finrank K E2 at this
    rwa [← sup_toSubalgebra_of_left] at this
  rw [FiniteDimensional]; rw [← rank_lt_aleph0_iff]; rw [not_lt] at h
have := LinearMap.rank_le

中文:
定理 finrank_sup_le
  证明: by
  by_cases h : FiniteDimensional K E1
  · have := E1.toSubalgebra.finrank_sup_le_of_free E2.toSubalgebra
    change _ <= finrank K E1 * finrank K E2 at this
    rwa [← sup_toSubalgebra_of_left] at this
  rw [FiniteDimensional]; rw [← rank_lt_aleph0_iff]; rw [not_lt] at h
have := LinearMap.rank_le

Depends on / 依赖: Cardinal, Cardinal.toNat_apply_of_aleph0_le, E1.toSubalgebra, E1.toSubalgebra.finrank_sup_le_of_free, E2.toSubalgebra, FiniteDimensional, LinearMap, LinearMap.rank_le_of_injective, Subalgebra, Subalgebra.toSubmodule, Submodule, Submodule.inclusion_injective, finrank, finrank_sup_le_of_free, inclusion_injective, not_lt, rank_le_of_injective, rank_lt_aleph0_iff, sup_toSubalgebra_of_left, toNat_apply_of_aleph0_le
-/
theorem finrank_sup_le :
    finrank K ↥(E1 ⊔ E2) <= finrank K E1 * finrank K E2 := by
  by_cases h : FiniteDimensional K E1
  · have := E1.toSubalgebra.finrank_sup_le_of_free E2.toSubalgebra
    change _ <= finrank K E1 * finrank K E2 at this
    rwa [← sup_toSubalgebra_of_left] at this
  rw [FiniteDimensional]; rw [← rank_lt_aleph0_iff]; rw [not_lt] at h
have := LinearMap.rank_le_of_injective _ Submodule.inclusion_injective
    show Subalgebra.toSubmodule E1.toSubalgebra <= Subalgebra.toSubmodule (E1 ⊔ E2).toSubalgebra by
      simp
  rw [show finrank K E1 = 0 from Cardinal.toNat_apply_of_aleph0_le h]; rw [show finrank K ↥(E1 ⊔ E2) = 0 from Cardinal.toNat_apply_of_aleph0_le (h.trans this)]; rw [zero_mul]

variable {ι : Type*} {t : ι -> IntermediateField K L}

/--
theorem `coe_iSup_of_directed` / 定理 `coe_iSup_of_directed`

English:
theorem coe_iSup_of_directed
  given: [Nonempty ι] (dir : Directed (· <= ·) t)
  proof: let M : IntermediateField K L :=
    { __ := Subalgebra.copy _ _ (Subalgebra.coe_iSup_of_directed dir).symm
      inv_mem' := fun _ hx => have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (t i).inv_mem hi⟩ }
  have : iSup t = M := le_antisymm
    (iSup_le fun i => le_iSup (fun i =>

中文:
定理 coe_iSup_of_directed
  条件: [Nonempty ι] (dir : Directed (· <= ·) t)
  证明: let M : IntermediateField K L :=
    { __ := Subalgebra.copy _ _ (Subalgebra.coe_iSup_of_directed dir).symm
      inv_mem' := fun _ hx => have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (t i).inv_mem hi⟩ }
  have : iSup t = M := le_antisymm
    (iSup_le fun i => le_iSup (fun i =>

Depends on / 依赖: IntermediateField, Set.iUnion_subset, Set.mem_iUnion.mp, Set.mem_iUnion.mpr, Subalgebra, Subalgebra.coe_iSup_of_directed, Subalgebra.copy, coe_iSup_of_directed, iSup_le, iUnion_subset, inv_mem, le_antisymm, le_iSup, mem_iUnion, this.symm
-/
theorem coe_iSup_of_directed [Nonempty ι] (dir : Directed (· <= ·) t) :
    ↑(iSup t) = ⋃ i, (t i : Set L) :=
  let M : IntermediateField K L :=
    { __ := Subalgebra.copy _ _ (Subalgebra.coe_iSup_of_directed dir).symm
      inv_mem' := fun _ hx => have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (t i).inv_mem hi⟩ }
  have : iSup t = M := le_antisymm
    (iSup_le fun i => le_iSup (fun i => (t i : Set L)) i) (Set.iUnion_subset fun _ => le_iSup t _)
  this.symm ▸ rfl

/--
theorem `toSubalgebra_iSup_of_directed` / 定理 `toSubalgebra_iSup_of_directed`

English:
theorem toSubalgebra_iSup_of_directed
  given: (dir : Directed (· <= ·) t)
  proof: by
  cases isEmpty_or_nonempty ι
  · simp_rw [iSup_of_empty, bot_toSubalgebra]
  · exact SetLike.ext' ((coe_iSup_of_directed dir).trans (Subalgebra.coe_iSup_of_directed dir).symm)

中文:
定理 toSubalgebra_iSup_of_directed
  条件: (dir : Directed (· <= ·) t)
  证明: by
  cases isEmpty_or_nonempty ι
  · simp_rw [iSup_of_empty, bot_toSubalgebra]
  · exact SetLike.ext' ((coe_iSup_of_directed dir).trans (Subalgebra.coe_iSup_of_directed dir).symm)

Depends on / 依赖: SetLike, SetLike.ext, Subalgebra, Subalgebra.coe_iSup_of_directed, bot_toSubalgebra, coe_iSup_of_directed, iSup_of_empty, isEmpty_or_nonempty, simp_rw
-/
theorem toSubalgebra_iSup_of_directed (dir : Directed (· <= ·) t) :
    (iSup t).toSubalgebra = ⨆ i, (t i).toSubalgebra := by
  cases isEmpty_or_nonempty ι
  · simp_rw [iSup_of_empty, bot_toSubalgebra]
  · exact SetLike.ext' ((coe_iSup_of_directed dir).trans (Subalgebra.coe_iSup_of_directed dir).symm)

/--
Instance `finiteDimensional_iSup_of_finite` / 实例 `finiteDimensional_iSup_of_finite`

English:
instance finiteDimensional_iSup_of_finite
  signature: [h : Finite ι] [forall i, FiniteDimensional K (t i)]
  body: by
  rw [← iSup_univ]
  induction Set.univ, Set.finite_univ (α := ι) using Set.Finite.induction_on with
  | empty =>
    rw [iSup_emptyset]
    exact (botEquiv K L).symm.toLinearEquiv.finiteDimensional
  | insert s hs =>
    rw [iSup_insert]
    exact IntermediateField.finiteDimensional_sup _ _

中文:
实例 finiteDimensional_iSup_of_finite
  签名: [h : Finite ι] [对任意 i, FiniteDimensional K (t i)]
  定义体: by
  rw [← iSup_univ]
  induction Set.univ, Set.finite_univ (α := ι) using Set.Finite.induction_on with
  | empty =>
    rw [iSup_emptyset]
    exact (botEquiv K L).symm.toLinearEquiv.finiteDimensional
  | insert s hs =>
    rw [iSup_insert]
    exact IntermediateField.finiteDimensional_sup _ _

Depends on / 依赖: Finite, IntermediateField, IntermediateField.finiteDimensional_sup, Set.Finite.induction_on, Set.finite_univ, Set.univ, botEquiv, finiteDimensional, finiteDimensional_sup, finite_univ, iSup_emptyset, iSup_insert, iSup_univ, induction_on, insert, symm.toLinearEquiv.finiteDimensional, toLinearEquiv
-/
instance finiteDimensional_iSup_of_finite [h : Finite ι] [forall i, FiniteDimensional K (t i)] :
    FiniteDimensional K (⨆ i, t i : IntermediateField K L) := by
  rw [← iSup_univ]
  induction Set.univ, Set.finite_univ (α := ι) using Set.Finite.induction_on with
  | empty =>
    rw [iSup_emptyset]
    exact (botEquiv K L).symm.toLinearEquiv.finiteDimensional
  | insert s hs =>
    rw [iSup_insert]
    exact IntermediateField.finiteDimensional_sup _ _

/--
Instance `finiteDimensional_iSup_of_finset` / 实例 `finiteDimensional_iSup_of_finset`

English:
instance finiteDimensional_iSup_of_finset
  body: iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite

中文:
实例 finiteDimensional_iSup_of_finset
  定义体: iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite

Depends on / 依赖: IntermediateField, IntermediateField.finiteDimensional_iSup_of_finite, finiteDimensional_iSup_of_finite, iSup_subtype
-/
instance finiteDimensional_iSup_of_finset
    {s : Finset ι} [forall i, FiniteDimensional K (t i)] :
    FiniteDimensional K (⨆ i in s, t i : IntermediateField K L) :=
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite

/--
theorem `finiteDimensional_iSup_of_finset'` / 定理 `finiteDimensional_iSup_of_finset'`

English:
theorem finiteDimensional_iSup_of_finset'
  proof: have := Subtype.forall'.mp h
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite

中文:
定理 finiteDimensional_iSup_of_finset'
  证明: have := Subtype.forall'.mp h
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite

Depends on / 依赖: IntermediateField, IntermediateField.finiteDimensional_iSup_of_finite, Subtype, Subtype.forall, finiteDimensional_iSup_of_finite, iSup_subtype
-/
theorem finiteDimensional_iSup_of_finset'
    {s : Finset ι} (h : forall i in s, FiniteDimensional K (t i)) :
    FiniteDimensional K (⨆ i in s, t i : IntermediateField K L) :=
  have := Subtype.forall'.mp h
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite

/--
theorem `isSplittingField_iSup` / 定理 `isSplittingField_iSup`

English:
theorem isSplittingField_iSup
  statement: {p : ι -> K[X]}
  proof: by
  let F : IntermediateField K L := ⨆ i in s, t i
  have hF : forall i in s, t i <= F := fun i hi => le_iSup_of_le i (le_iSup (fun _ => t i) hi)
  simp only [isSplittingField_iff, Polynomial.map_prod] at h ⊢
  refine ⟨Splits.prod fun i hi => by
    simpa [Polynomial.map_map] using (h i hi).1.map (

中文:
定理 isSplittingField_iSup
  结论: {p : ι -> K[X]}
  证明: by
  let F : IntermediateField K L := ⨆ i in s, t i
  have hF : forall i in s, t i <= F := fun i hi => le_iSup_of_le i (le_iSup (fun _ => t i) hi)
  simp only [isSplittingField_iff, Polynomial.map_prod] at h ⊢
  refine ⟨Splits.prod fun i hi => by
    simpa [Polynomial.map_map] using (h i hi).1.map (

Depends on / 依赖: IntermediateField, Polynomial, Polynomial.map_map, Polynomial.map_prod, Set.iSup_eq_iUnion, Splits, Splits.prod, iSup_congr, iSup_eq_iUnion, inclusion, isSplittingField_iff, le_iSup, le_iSup_of_le, map_map, map_prod, rootSet_prod, toRingHom
-/
theorem isSplittingField_iSup {p : ι -> K[X]}
    {s : Finset ι} (h0 : ∏ i in s, p i != 0) (h : forall i in s, (p i).IsSplittingField K (t i)) :
    (∏ i in s, p i).IsSplittingField K (⨆ i in s, t i : IntermediateField K L) := by
  let F : IntermediateField K L := ⨆ i in s, t i
  have hF : forall i in s, t i <= F := fun i hi => le_iSup_of_le i (le_iSup (fun _ => t i) hi)
  simp only [isSplittingField_iff, Polynomial.map_prod] at h ⊢
  refine ⟨Splits.prod fun i hi => by
    simpa [Polynomial.map_map] using (h i hi).1.map (inclusion (hF i hi)).toRingHom, ?_⟩
  simp only [rootSet_prod p s h0, ← Set.iSup_eq_iUnion, (@gc K _ L _ _).l_iSup₂]
  exact iSup_congr fun i => iSup_congr fun hi => (h i hi).2

end Supremum

section Tower

variable (E)
variable {K : Type*} [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

/--
theorem `adjoin_rank_le_of_isAlgebraic` / 定理 `adjoin_rank_le_of_isAlgebraic`

English:
theorem adjoin_rank_le_of_isAlgebraic
  statement: (L : IntermediateField F K)
  proof: by
  have h : (adjoin E (L.toSubalgebra : Set K)).toSubalgebra =
      Algebra.adjoin E (L.toSubalgebra : Set K) :=
    L.adjoin_intermediateField_toSubalgebra_of_isAlgebraic E halg
  have := L.toSubalgebra.adjoin_rank_le E
  rwa [(Subalgebra.equivOfEq _ _ h).symm.toLinearEquiv.rank_eq] at this

中文:
定理 adjoin_rank_le_of_isAlgebraic
  结论: (L : 整数ermediateField F K)
  证明: by
  have h : (adjoin E (L.toSubalgebra : Set K)).toSubalgebra =
      Algebra.adjoin E (L.toSubalgebra : Set K) :=
    L.adjoin_intermediateField_toSubalgebra_of_isAlgebraic E halg
  have := L.toSubalgebra.adjoin_rank_le E
  rwa [(Subalgebra.equivOfEq _ _ h).symm.toLinearEquiv.rank_eq] at this

Depends on / 依赖: Algebra, Algebra.adjoin, L.adjoin_intermediateField_toSubalgebra_of_isAlgebraic, L.toSubalgebra, L.toSubalgebra.adjoin_rank_le, Subalgebra, Subalgebra.equivOfEq, adjoin, adjoin_intermediateField_toSubalgebra_of_isAlgebraic, adjoin_rank_le, equivOfEq, rank_eq, symm.toLinearEquiv.rank_eq, toLinearEquiv, toSubalgebra
-/
theorem adjoin_rank_le_of_isAlgebraic (L : IntermediateField F K)
    (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) :
    Module.rank E (adjoin E (L : Set K)) <= Module.rank F L := by
  have h : (adjoin E (L.toSubalgebra : Set K)).toSubalgebra =
      Algebra.adjoin E (L.toSubalgebra : Set K) :=
    L.adjoin_intermediateField_toSubalgebra_of_isAlgebraic E halg
  have := L.toSubalgebra.adjoin_rank_le E
  rwa [(Subalgebra.equivOfEq _ _ h).symm.toLinearEquiv.rank_eq] at this

/--
theorem `adjoin_rank_le_of_isAlgebraic_left` / 定理 `adjoin_rank_le_of_isAlgebraic_left`

English:
theorem adjoin_rank_le_of_isAlgebraic_left
  statement: (L : IntermediateField F K)
  proof: adjoin_rank_le_of_isAlgebraic E L (Or.inl halg)

中文:
定理 adjoin_rank_le_of_isAlgebraic_left
  结论: (L : 整数ermediateField F K)
  证明: adjoin_rank_le_of_isAlgebraic E L (Or.inl halg)

Depends on / 依赖: Or.inl, adjoin_rank_le_of_isAlgebraic
-/
theorem adjoin_rank_le_of_isAlgebraic_left (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F E] :
    Module.rank E (adjoin E (L : Set K)) <= Module.rank F L :=
  adjoin_rank_le_of_isAlgebraic E L (Or.inl halg)

/--
theorem `adjoin_rank_le_of_isAlgebraic_right` / 定理 `adjoin_rank_le_of_isAlgebraic_right`

English:
theorem adjoin_rank_le_of_isAlgebraic_right
  statement: (L : IntermediateField F K)
  proof: adjoin_rank_le_of_isAlgebraic E L (Or.inr halg)

中文:
定理 adjoin_rank_le_of_isAlgebraic_right
  结论: (L : 整数ermediateField F K)
  证明: adjoin_rank_le_of_isAlgebraic E L (Or.inr halg)

Depends on / 依赖: Or.inr, adjoin_rank_le_of_isAlgebraic
-/
theorem adjoin_rank_le_of_isAlgebraic_right (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F L] :
    Module.rank E (adjoin E (L : Set K)) <= Module.rank F L :=
  adjoin_rank_le_of_isAlgebraic E L (Or.inr halg)

end Tower

open Set CompleteLattice

/--
theorem `adjoin_simple_isCompactElement` / 定理 `adjoin_simple_isCompactElement`

English:
theorem adjoin_simple_isCompactElement
  given: (x : E)
  statement: IsCompactElement F⟮x⟯
  proof: by
  simp_rw [isCompactElement_iff_le_of_directed_sSup_le,
    adjoin_simple_le_iff, sSup_eq_iSup', ← exists_prop]
  intro s hne hs hx
  have := hne.to_subtype
  rwa [← SetLike.mem_coe, coe_iSup_of_directed hs.directed_val, mem_iUnion, Subtype.exists] at hx

中文:
定理 adjoin_simple_isCompactElement
  条件: (x : E)
  结论: IsCompactElement F⟮x⟯
  证明: by
  simp_rw [isCompactElement_iff_le_of_directed_sSup_le,
    adjoin_simple_le_iff, sSup_eq_iSup', ← exists_prop]
  intro s hne hs hx
  have := hne.to_subtype
  rwa [← SetLike.mem_coe, coe_iSup_of_directed hs.directed_val, mem_iUnion, Subtype.exists] at hx

Depends on / 依赖: SetLike, SetLike.mem_coe, Subtype, Subtype.exists, adjoin_simple_le_iff, coe_iSup_of_directed, directed_val, exists_prop, hne.to_subtype, hs.directed_val, isCompactElement_iff_le_of_directed_sSup_le, mem_coe, mem_iUnion, sSup_eq_iSup, simp_rw, to_subtype
-/
theorem adjoin_simple_isCompactElement (x : E) : IsCompactElement F⟮x⟯ := by
  simp_rw [isCompactElement_iff_le_of_directed_sSup_le,
    adjoin_simple_le_iff, sSup_eq_iSup', ← exists_prop]
  intro s hne hs hx
  have := hne.to_subtype
  rwa [← SetLike.mem_coe, coe_iSup_of_directed hs.directed_val, mem_iUnion, Subtype.exists] at hx

/--
theorem `adjoin_finset_isCompactElement` / 定理 `adjoin_finset_isCompactElement`

English:
theorem adjoin_finset_isCompactElement
  given: (S : Finset E)
  proof: by
  rw [← biSup_adjoin_simple]
  simp_rw [Finset.mem_coe, ← Finset.sup_eq_iSup]
  exact isCompactElement_finsetSup S fun x _ => adjoin_simple_isCompactElement x

中文:
定理 adjoin_finset_isCompactElement
  条件: (S : Finset E)
  证明: by
  rw [← biSup_adjoin_simple]
  simp_rw [Finset.mem_coe, ← Finset.sup_eq_iSup]
  exact isCompactElement_finsetSup S fun x _ => adjoin_simple_isCompactElement x

Depends on / 依赖: Finset, Finset.mem_coe, Finset.sup_eq_iSup, adjoin_simple_isCompactElement, biSup_adjoin_simple, isCompactElement_finsetSup, mem_coe, simp_rw, sup_eq_iSup
-/
theorem adjoin_finset_isCompactElement (S : Finset E) :
    IsCompactElement (adjoin F S : IntermediateField F E) := by
  rw [← biSup_adjoin_simple]
  simp_rw [Finset.mem_coe, ← Finset.sup_eq_iSup]
  exact isCompactElement_finsetSup S fun x _ => adjoin_simple_isCompactElement x

/--
theorem `adjoin_finite_isCompactElement` / 定理 `adjoin_finite_isCompactElement`

English:
theorem adjoin_finite_isCompactElement
  given: {S : Set E} (h : S.Finite)
  statement: IsCompactElement (adjoin F S)
  proof: Finite.coe_toFinset h ▸ adjoin_finset_isCompactElement h.toFinset

中文:
定理 adjoin_finite_isCompactElement
  条件: {S : Set E} (h : S.Finite)
  结论: IsCompactElement (adjoin F S)
  证明: Finite.coe_toFinset h ▸ adjoin_finset_isCompactElement h.toFinset

Depends on / 依赖: Finite, Finite.coe_toFinset, adjoin_finset_isCompactElement, coe_toFinset, h.toFinset, toFinset
-/
theorem adjoin_finite_isCompactElement {S : Set E} (h : S.Finite) : IsCompactElement (adjoin F S) :=
  Finite.coe_toFinset h ▸ adjoin_finset_isCompactElement h.toFinset

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCompactlyGenerated (IntermediateField F E)
  body: ⟨fun s =>
    ⟨(fun x => F⟮x⟯) '' s,
      ⟨by rintro t ⟨x, _, rfl⟩; exact adjoin_simple_isCompactElement x,
sSup_image.trans (biSup_adjoin_simple _).trans
le_antisymm (adjoin_le_iff.mpr le_rfl) subset_adjoin F (s : Set E)⟩⟩⟩

中文:
实例 :
  签名: IsCompactlyGenerated (整数ermediateField F E)
  定义体: ⟨fun s =>
    ⟨(fun x => F⟮x⟯) '' s,
      ⟨by rintro t ⟨x, _, rfl⟩; exact adjoin_simple_isCompactElement x,
sSup_image.trans (biSup_adjoin_simple _).trans
le_antisymm (adjoin_le_iff.mpr le_rfl) subset_adjoin F (s : Set E)⟩⟩⟩

Depends on / 依赖: adjoin_le_iff, adjoin_le_iff.mpr, adjoin_simple_isCompactElement, biSup_adjoin_simple, le_antisymm, le_rfl, sSup_image, sSup_image.trans, subset_adjoin
-/
instance : IsCompactlyGenerated (IntermediateField F E) :=
  ⟨fun s =>
    ⟨(fun x => F⟮x⟯) '' s,
      ⟨by rintro t ⟨x, _, rfl⟩; exact adjoin_simple_isCompactElement x,
sSup_image.trans (biSup_adjoin_simple _).trans
le_antisymm (adjoin_le_iff.mpr le_rfl) subset_adjoin F (s : Set E)⟩⟩⟩

/--
theorem `exists_finset_of_mem_iSup` / 定理 `exists_finset_of_mem_iSup`

English:
theorem exists_finset_of_mem_iSup
  statement: {ι : Type*} {f : ι -> IntermediateField F E} {x : E}
  proof: by
  have := (adjoin_simple_isCompactElement x).exists_finset_of_le_iSup (IntermediateField F E) f
  simp only [adjoin_simple_le_iff] at this
  exact this hx

中文:
定理 exists_finset_of_mem_iSup
  结论: {ι : 类型} {f : ι -> 整数ermediateField F E} {x : E}
  证明: by
  have := (adjoin_simple_isCompactElement x).exists_finset_of_le_iSup (IntermediateField F E) f
  simp only [adjoin_simple_le_iff] at this
  exact this hx

Depends on / 依赖: IntermediateField, adjoin_simple_isCompactElement, adjoin_simple_le_iff, exists_finset_of_le_iSup
-/
theorem exists_finset_of_mem_iSup {ι : Type*} {f : ι -> IntermediateField F E} {x : E}
    (hx : x in ⨆ i, f i) : exists s : Finset ι, x in ⨆ i in s, f i := by
  have := (adjoin_simple_isCompactElement x).exists_finset_of_le_iSup (IntermediateField F E) f
  simp only [adjoin_simple_le_iff] at this
  exact this hx

/--
theorem `exists_finset_of_mem_supr'` / 定理 `exists_finset_of_mem_supr'`

English:
theorem exists_finset_of_mem_supr'
  statement: {ι : Type*} {f : ι -> IntermediateField F E} {x : E}
  proof: by
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le fun i x h => ?_) hx)
  exact SetLike.le_def.mp (le_iSup_of_le ⟨i, x, h⟩ (by simp)) (mem_adjoin_simple_self F x)

中文:
定理 exists_finset_of_mem_supr'
  结论: {ι : 类型} {f : ι -> 整数ermediateField F E} {x : E}
  证明: by
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le fun i x h => ?_) hx)
  exact SetLike.le_def.mp (le_iSup_of_le ⟨i, x, h⟩ (by simp)) (mem_adjoin_simple_self F x)

Depends on / 依赖: SetLike, SetLike.le_def.mp, exists_finset_of_mem_iSup, iSup_le, le_def, le_iSup_of_le, mem_adjoin_simple_self
-/
theorem exists_finset_of_mem_supr' {ι : Type*} {f : ι -> IntermediateField F E} {x : E}
    (hx : x in ⨆ i, f i) : exists s : Finset (Σ i, f i), x in ⨆ i in s, F⟮(i.2 : E)⟯ := by
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le fun i x h => ?_) hx)
  exact SetLike.le_def.mp (le_iSup_of_le ⟨i, x, h⟩ (by simp)) (mem_adjoin_simple_self F x)

/--
theorem `exists_finset_of_mem_supr''` / 定理 `exists_finset_of_mem_supr''`

English:
theorem exists_finset_of_mem_supr''
  statement: {ι : Type*} {f : ι -> IntermediateField F E}
  proof: by
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le (fun i x1 hx1 => ?_)) hx)
  refine SetLike.le_def.mp (le_iSup_of_le ⟨i, x1, hx1⟩ ?_)
    (subset_adjoin F (rootSet (minpoly F x1) E) ?_)
  · rw [IntermediateField.minpoly_eq, Subtype.coe_mk]
  · rw [mem_rootSet_of_ne, minpoly.aeval]
 

中文:
定理 exists_finset_of_mem_supr''
  结论: {ι : 类型} {f : ι -> 整数ermediateField F E}
  证明: by
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le (fun i x1 hx1 => ?_)) hx)
  refine SetLike.le_def.mp (le_iSup_of_le ⟨i, x1, hx1⟩ ?_)
    (subset_adjoin F (rootSet (minpoly F x1) E) ?_)
  · rw [IntermediateField.minpoly_eq, Subtype.coe_mk]
  · rw [mem_rootSet_of_ne, minpoly.aeval]
 

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IntermediateField, IntermediateField.minpoly_eq, IsIntegral, SetLike, SetLike.le_def.mp, Subtype, Subtype.coe_mk, coe_mk, exists_finset_of_mem_iSup, iSup_le, isIntegral, isIntegral_iff, isIntegral_iff.mp, le_def, le_iSup_of_le, mem_rootSet_of_ne, minpoly, minpoly.aeval
-/
theorem exists_finset_of_mem_supr'' {ι : Type*} {f : ι -> IntermediateField F E}
    (h : forall i, Algebra.IsAlgebraic F (f i)) {x : E} (hx : x in ⨆ i, f i) :
    exists s : Finset (Σ i, f i), x in ⨆ i in s, adjoin F ((minpoly F (i.2 :)).rootSet E) := by
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le (fun i x1 hx1 => ?_)) hx)
  refine SetLike.le_def.mp (le_iSup_of_le ⟨i, x1, hx1⟩ ?_)
    (subset_adjoin F (rootSet (minpoly F x1) E) ?_)
  · rw [IntermediateField.minpoly_eq, Subtype.coe_mk]
  · rw [mem_rootSet_of_ne, minpoly.aeval]
    exact minpoly.ne_zero (isIntegral_iff.mp (Algebra.IsIntegral.isIntegral (⟨x1, hx1⟩ : f i)))

/--
theorem `exists_finset_of_mem_adjoin` / 定理 `exists_finset_of_mem_adjoin`

English:
theorem exists_finset_of_mem_adjoin
  given: {S : Set E} {x : E} (hx : x in adjoin F S)
  proof: by
  simp_rw [← biSup_adjoin_simple S, ← iSup_subtype''] at hx
  obtain ⟨s, hx'⟩ := exists_finset_of_mem_iSup hx
  classical
  refine ⟨s.image Subtype.val, by simp, SetLike.le_def.mp ?_ hx'⟩
  simp_rw [Finset.coe_image, iSup_le_iff, adjoin_le_iff]
  rintro _ h _ rfl
  exact subset_adjoin F _ ⟨_, h, 

中文:
定理 exists_finset_of_mem_adjoin
  条件: {S : Set E} {x : E} (hx : x in adjoin F S)
  证明: by
  simp_rw [← biSup_adjoin_simple S, ← iSup_subtype''] at hx
  obtain ⟨s, hx'⟩ := exists_finset_of_mem_iSup hx
  classical
  refine ⟨s.image Subtype.val, by simp, SetLike.le_def.mp ?_ hx'⟩
  simp_rw [Finset.coe_image, iSup_le_iff, adjoin_le_iff]
  rintro _ h _ rfl
  exact subset_adjoin F _ ⟨_, h, 

Depends on / 依赖: Finset, Finset.coe_image, SetLike, SetLike.le_def.mp, Subtype, Subtype.val, adjoin_le_iff, biSup_adjoin_simple, classical, coe_image, exists_finset_of_mem_iSup, iSup_le_iff, iSup_subtype, le_def, s.image, simp_rw, subset_adjoin
-/
theorem exists_finset_of_mem_adjoin {S : Set E} {x : E} (hx : x in adjoin F S) :
    exists T : Finset E, (T : Set E) subseteq S ∧ x in adjoin F (T : Set E) := by
  simp_rw [← biSup_adjoin_simple S, ← iSup_subtype''] at hx
  obtain ⟨s, hx'⟩ := exists_finset_of_mem_iSup hx
  classical
  refine ⟨s.image Subtype.val, by simp, SetLike.le_def.mp ?_ hx'⟩
  simp_rw [Finset.coe_image, iSup_le_iff, adjoin_le_iff]
  rintro _ h _ rfl
  exact subset_adjoin F _ ⟨_, h, rfl⟩

end AdjoinDef

section AdjoinIntermediateFieldLattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {α : E} {S : Set E}

section AdjoinRank

open Module Module

variable {K L : IntermediateField F E}

@[simp]
/--
theorem `rank_eq_one_iff` / 定理 `rank_eq_one_iff`

English:
theorem rank_eq_one_iff
  statement: Module.rank F K = 1 ↔ K = ⊥
  proof: by
  rw [← toSubalgebra_inj]; rw [← rank_eq_rank_subalgebra]; rw [Subalgebra.rank_eq_one_iff]; rw [bot_toSubalgebra]

@[simp]

中文:
定理 rank_eq_one_iff
  结论: Module.rank F K = 1 ↔ K = ⊥
  证明: by
  rw [← toSubalgebra_inj]; rw [← rank_eq_rank_subalgebra]; rw [Subalgebra.rank_eq_one_iff]; rw [bot_toSubalgebra]

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.rank_eq_one_iff, bot_toSubalgebra, rank_eq_one_iff, rank_eq_rank_subalgebra, toSubalgebra_inj
-/
theorem rank_eq_one_iff : Module.rank F K = 1 ↔ K = ⊥ := by
  rw [← toSubalgebra_inj]; rw [← rank_eq_rank_subalgebra]; rw [Subalgebra.rank_eq_one_iff]; rw [bot_toSubalgebra]

@[simp]
/--
theorem `finrank_eq_one_iff` / 定理 `finrank_eq_one_iff`

English:
theorem finrank_eq_one_iff
  statement: finrank F K = 1 ↔ K = ⊥
  proof: by
  rw [← toSubalgebra_inj]; rw [← finrank_eq_finrank_subalgebra]; rw [Subalgebra.finrank_eq_one_iff]; rw [bot_toSubalgebra]

@[simp]

中文:
定理 finrank_eq_one_iff
  结论: finrank F K = 1 ↔ K = ⊥
  证明: by
  rw [← toSubalgebra_inj]; rw [← finrank_eq_finrank_subalgebra]; rw [Subalgebra.finrank_eq_one_iff]; rw [bot_toSubalgebra]

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.finrank_eq_one_iff, bot_toSubalgebra, finrank_eq_finrank_subalgebra, finrank_eq_one_iff, toSubalgebra_inj
-/
theorem finrank_eq_one_iff : finrank F K = 1 ↔ K = ⊥ := by
  rw [← toSubalgebra_inj]; rw [← finrank_eq_finrank_subalgebra]; rw [Subalgebra.finrank_eq_one_iff]; rw [bot_toSubalgebra]

@[simp]
/--
theorem `rank_bot` / 定理 `rank_bot`

English:
theorem rank_bot
  statement: Module.rank F (⊥ : IntermediateField F E) = 1
  proof: by
  rw [rank_eq_one_iff]

@[simp]

中文:
定理 rank_bot
  结论: Module.rank F (⊥ : 整数ermediateField F E) = 1
  证明: by
  rw [rank_eq_one_iff]

@[simp]
-/
protected theorem rank_bot : Module.rank F (⊥ : IntermediateField F E) = 1 := by
  rw [rank_eq_one_iff]

@[simp]
/--
theorem `finrank_bot` / 定理 `finrank_bot`

English:
theorem finrank_bot
  statement: finrank F (⊥ : IntermediateField F E) = 1
  proof: by
  rw [finrank_eq_one_iff]

中文:
定理 finrank_bot
  结论: finrank F (⊥ : 整数ermediateField F E) = 1
  证明: by
  rw [finrank_eq_one_iff]
-/
protected theorem finrank_bot : finrank F (⊥ : IntermediateField F E) = 1 := by
  rw [finrank_eq_one_iff]

/--
theorem `rank_bot'` / 定理 `rank_bot'`

English:
theorem rank_bot'
  statement: Module.rank (⊥ : IntermediateField F E) E = Module.rank F E
  proof: by
  rw [← rank_mul_rank F (⊥ : IntermediateField F E) E]; rw [IntermediateField.rank_bot]; rw [one_mul]

@[simp]

中文:
定理 rank_bot'
  结论: Module.rank (⊥ : 整数ermediateField F E) E = Module.rank F E
  证明: by
  rw [← rank_mul_rank F (⊥ : IntermediateField F E) E]; rw [IntermediateField.rank_bot]; rw [one_mul]

@[simp]
-/
@[simp] theorem rank_bot' : Module.rank (⊥ : IntermediateField F E) E = Module.rank F E := by
  rw [← rank_mul_rank F (⊥ : IntermediateField F E) E]; rw [IntermediateField.rank_bot]; rw [one_mul]

@[simp]
/--
theorem `finrank_bot'` / 定理 `finrank_bot'`

English:
theorem finrank_bot'
  statement: finrank (⊥ : IntermediateField F E) E = finrank F E
  proof: congr(Cardinal.toNat $(rank_bot'))

中文:
定理 finrank_bot'
  结论: finrank (⊥ : 整数ermediateField F E) E = finrank F E
  证明: congr(Cardinal.toNat $(rank_bot'))

Depends on / 依赖: Cardinal, Cardinal.toNat, rank_bot
-/
theorem finrank_bot' : finrank (⊥ : IntermediateField F E) E = finrank F E :=
  congr(Cardinal.toNat $(rank_bot'))

/--
theorem `rank_top` / 定理 `rank_top`

English:
theorem rank_top
  statement: Module.rank (⊤ : IntermediateField F E) E = 1
  proof: Subalgebra.bot_eq_top_iff_rank_eq_one.mp top_le_iff.mp fun x _ => ⟨⟨x, trivial⟩, rfl⟩

@[simp]

中文:
定理 rank_top
  结论: Module.rank (⊤ : 整数ermediateField F E) E = 1
  证明: Subalgebra.bot_eq_top_iff_rank_eq_one.mp top_le_iff.mp fun x _ => ⟨⟨x, trivial⟩, rfl⟩

@[simp]
-/
@[simp] protected theorem rank_top : Module.rank (⊤ : IntermediateField F E) E = 1 :=
Subalgebra.bot_eq_top_iff_rank_eq_one.mp top_le_iff.mp fun x _ => ⟨⟨x, trivial⟩, rfl⟩

@[simp]
/--
theorem `finrank_top` / 定理 `finrank_top`

English:
theorem finrank_top
  statement: finrank (⊤ : IntermediateField F E) E = 1
  proof: rank_eq_one_iff_finrank_eq_one.mp IntermediateField.rank_top

中文:
定理 finrank_top
  结论: finrank (⊤ : 整数ermediateField F E) E = 1
  证明: rank_eq_one_iff_finrank_eq_one.mp IntermediateField.rank_top
-/
protected theorem finrank_top : finrank (⊤ : IntermediateField F E) E = 1 :=
  rank_eq_one_iff_finrank_eq_one.mp IntermediateField.rank_top

/--
theorem `rank_top'` / 定理 `rank_top'`

English:
theorem rank_top'
  statement: Module.rank F (⊤ : IntermediateField F E) = Module.rank F E
  proof: rank_top F E

中文:
定理 rank_top'
  结论: Module.rank F (⊤ : 整数ermediateField F E) = Module.rank F E
  证明: rank_top F E
-/
@[simp] theorem rank_top' : Module.rank F (⊤ : IntermediateField F E) = Module.rank F E :=
  rank_top F E

/--
theorem `finrank_top'` / 定理 `finrank_top'`

English:
theorem finrank_top'
  statement: finrank F (⊤ : IntermediateField F E) = finrank F E
  proof: finrank_top F E

中文:
定理 finrank_top'
  结论: finrank F (⊤ : 整数ermediateField F E) = finrank F E
  证明: finrank_top F E
-/
@[simp] theorem finrank_top' : finrank F (⊤ : IntermediateField F E) = finrank F E :=
  finrank_top F E

/--
lemma `finrank_eq_one_iff_eq_top` / 引理 `finrank_eq_one_iff_eq_top`

English:
lemma finrank_eq_one_iff_eq_top
  given: {K : IntermediateField F E}
  proof: by
  refine ⟨?_, (· ▸ IntermediateField.finrank_top)⟩
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]; rw [← top_le_iff]; rw [← top_le_iff]
  intro H x _
  obtain ⟨x, rfl⟩ := @H x IntermediateField.mem_top
  exact x.2

中文:
引理 finrank_eq_one_iff_eq_top
  条件: {K : 整数ermediateField F E}
  证明: by
  refine ⟨?_, (· ▸ IntermediateField.finrank_top)⟩
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]; rw [← top_le_iff]; rw [← top_le_iff]
  intro H x _
  obtain ⟨x, rfl⟩ := @H x IntermediateField.mem_top
  exact x.2

Depends on / 依赖: IntermediateField, IntermediateField.finrank_top, IntermediateField.mem_top, Subalgebra, Subalgebra.bot_eq_top_iff_finrank_eq_one, bot_eq_top_iff_finrank_eq_one, finrank_top, mem_top, top_le_iff
-/
lemma finrank_eq_one_iff_eq_top {K : IntermediateField F E} :
    Module.finrank K E = 1 ↔ K = ⊤ := by
  refine ⟨?_, (· ▸ IntermediateField.finrank_top)⟩
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]; rw [← top_le_iff]; rw [← top_le_iff]
  intro H x _
  obtain ⟨x, rfl⟩ := @H x IntermediateField.mem_top
  exact x.2

/--
theorem `bot_eq_top_iff_finrank_eq_one` / 定理 `bot_eq_top_iff_finrank_eq_one`

English:
theorem bot_eq_top_iff_finrank_eq_one
  proof: by
  rw [← IntermediateField.finrank_bot']; rw [← finrank_eq_one_iff_eq_top]

中文:
定理 bot_eq_top_iff_finrank_eq_one
  证明: by
  rw [← IntermediateField.finrank_bot']; rw [← finrank_eq_one_iff_eq_top]

Depends on / 依赖: IntermediateField, IntermediateField.finrank_bot, finrank_bot, finrank_eq_one_iff_eq_top
-/
theorem bot_eq_top_iff_finrank_eq_one :
    (⊥ : IntermediateField F E) = ⊤ ↔ Module.finrank F E = 1 := by
  rw [← IntermediateField.finrank_bot']; rw [← finrank_eq_one_iff_eq_top]

variable (F E) in
/--
theorem `isSimpleOrder_of_finrank_prime` / 定理 `isSimpleOrder_of_finrank_prime`

English:
theorem isSimpleOrder_of_finrank_prime
  given: (hp : Nat.Prime (Module.finrank F E))
  proof: by
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · exact ⟨⊥, ⊤, fun h => Nat.prime_one_false (bot_eq_top_iff_finrank_eq_one.mp h ▸ hp)⟩
  · intro K
    simpa [← toSubalgebra_strictMono.apply_eq_bot_iff, ← toSubalgebra_strictMono.apply_eq_top_iff]
      using (Subalgebra.isSimpleOrder_of_

中文:
定理 isSimpleOrder_of_finrank_prime
  条件: (hp : 自然数.Prime (Module.finrank F E))
  证明: by
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · exact ⟨⊥, ⊤, fun h => Nat.prime_one_false (bot_eq_top_iff_finrank_eq_one.mp h ▸ hp)⟩
  · intro K
    simpa [← toSubalgebra_strictMono.apply_eq_bot_iff, ← toSubalgebra_strictMono.apply_eq_top_iff]
      using (Subalgebra.isSimpleOrder_of_

Depends on / 依赖: K.toSubalgebra, Nat.prime_one_false, Subalgebra, Subalgebra.isSimpleOrder_of_finrank_prime, apply_eq_bot_iff, apply_eq_top_iff, bot_eq_top_iff_finrank_eq_one, bot_eq_top_iff_finrank_eq_one.mp, eq_bot_or_eq_top, isSimpleOrder_of_finrank_prime, prime_one_false, toNontrivial, toSubalgebra, toSubalgebra_strictMono, toSubalgebra_strictMono.apply_eq_bot_iff, toSubalgebra_strictMono.apply_eq_top_iff
-/
theorem isSimpleOrder_of_finrank_prime (hp : Nat.Prime (Module.finrank F E)) :
    IsSimpleOrder (IntermediateField F E) := by
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · exact ⟨⊥, ⊤, fun h => Nat.prime_one_false (bot_eq_top_iff_finrank_eq_one.mp h ▸ hp)⟩
  · intro K
    simpa [← toSubalgebra_strictMono.apply_eq_bot_iff, ← toSubalgebra_strictMono.apply_eq_top_iff]
      using (Subalgebra.isSimpleOrder_of_finrank_prime _ _ hp).eq_bot_or_eq_top K.toSubalgebra

/--
theorem `rank_adjoin_eq_one_iff` / 定理 `rank_adjoin_eq_one_iff`

English:
theorem rank_adjoin_eq_one_iff
  statement: Module.rank F (adjoin F S) = 1 ↔ S subseteq (⊥ : IntermediateField F E)
  proof: Iff.trans rank_eq_one_iff adjoin_eq_bot_iff

中文:
定理 rank_adjoin_eq_one_iff
  结论: Module.rank F (adjoin F S) = 1 ↔ S subseteq (⊥ : 整数ermediateField F E)
  证明: Iff.trans rank_eq_one_iff adjoin_eq_bot_iff

Depends on / 依赖: Iff.trans, adjoin_eq_bot_iff, rank_eq_one_iff
-/
theorem rank_adjoin_eq_one_iff : Module.rank F (adjoin F S) = 1 ↔ S subseteq (⊥ : IntermediateField F E) :=
  Iff.trans rank_eq_one_iff adjoin_eq_bot_iff

/--
theorem `rank_adjoin_simple_eq_one_iff` / 定理 `rank_adjoin_simple_eq_one_iff`

English:
theorem rank_adjoin_simple_eq_one_iff
  proof: by
  rw [rank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff

中文:
定理 rank_adjoin_simple_eq_one_iff
  证明: by
  rw [rank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff

Depends on / 依赖: Set.singleton_subset_iff, rank_adjoin_eq_one_iff, singleton_subset_iff
-/
theorem rank_adjoin_simple_eq_one_iff :
    Module.rank F F⟮α⟯ = 1 ↔ α in (⊥ : IntermediateField F E) := by
  rw [rank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff

/--
theorem `finrank_adjoin_eq_one_iff` / 定理 `finrank_adjoin_eq_one_iff`

English:
theorem finrank_adjoin_eq_one_iff
  statement: finrank F (adjoin F S) = 1 ↔ S subseteq (⊥ : IntermediateField F E)
  proof: Iff.trans finrank_eq_one_iff adjoin_eq_bot_iff

中文:
定理 finrank_adjoin_eq_one_iff
  结论: finrank F (adjoin F S) = 1 ↔ S subseteq (⊥ : 整数ermediateField F E)
  证明: Iff.trans finrank_eq_one_iff adjoin_eq_bot_iff

Depends on / 依赖: Iff.trans, adjoin_eq_bot_iff, finrank_eq_one_iff
-/
theorem finrank_adjoin_eq_one_iff : finrank F (adjoin F S) = 1 ↔ S subseteq (⊥ : IntermediateField F E) :=
  Iff.trans finrank_eq_one_iff adjoin_eq_bot_iff

/--
theorem `finrank_adjoin_simple_eq_one_iff` / 定理 `finrank_adjoin_simple_eq_one_iff`

English:
theorem finrank_adjoin_simple_eq_one_iff
  proof: by
  rw [finrank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff

中文:
定理 finrank_adjoin_simple_eq_one_iff
  证明: by
  rw [finrank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff

Depends on / 依赖: Set.singleton_subset_iff, finrank_adjoin_eq_one_iff, singleton_subset_iff
-/
theorem finrank_adjoin_simple_eq_one_iff :
    finrank F F⟮α⟯ = 1 ↔ α in (⊥ : IntermediateField F E) := by
  rw [finrank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff

/--
theorem `bot_eq_top_of_rank_adjoin_eq_one` / 定理 `bot_eq_top_of_rank_adjoin_eq_one`

English:
theorem bot_eq_top_of_rank_adjoin_eq_one
  given: (h : forall x : E, Module.rank F F⟮x⟯ = 1)
  proof: by
  ext y
  rw [iff_true_right IntermediateField.mem_top]
  exact rank_adjoin_simple_eq_one_iff.mp (h y)

中文:
定理 bot_eq_top_of_rank_adjoin_eq_one
  条件: (h : 对任意 x : E, Module.rank F F⟮x⟯ = 1)
  证明: by
  ext y
  rw [iff_true_right IntermediateField.mem_top]
  exact rank_adjoin_simple_eq_one_iff.mp (h y)

Depends on / 依赖: IntermediateField, IntermediateField.mem_top, iff_true_right, mem_top, rank_adjoin_simple_eq_one_iff, rank_adjoin_simple_eq_one_iff.mp
-/
theorem bot_eq_top_of_rank_adjoin_eq_one (h : forall x : E, Module.rank F F⟮x⟯ = 1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  ext y
  rw [iff_true_right IntermediateField.mem_top]
  exact rank_adjoin_simple_eq_one_iff.mp (h y)

/--
theorem `bot_eq_top_of_finrank_adjoin_eq_one` / 定理 `bot_eq_top_of_finrank_adjoin_eq_one`

English:
theorem bot_eq_top_of_finrank_adjoin_eq_one
  given: (h : forall x : E, finrank F F⟮x⟯ = 1)
  proof: by
  ext y
  rw [iff_true_right IntermediateField.mem_top]
  exact finrank_adjoin_simple_eq_one_iff.mp (h y)

中文:
定理 bot_eq_top_of_finrank_adjoin_eq_one
  条件: (h : 对任意 x : E, finrank F F⟮x⟯ = 1)
  证明: by
  ext y
  rw [iff_true_right IntermediateField.mem_top]
  exact finrank_adjoin_simple_eq_one_iff.mp (h y)

Depends on / 依赖: IntermediateField, IntermediateField.mem_top, finrank_adjoin_simple_eq_one_iff, finrank_adjoin_simple_eq_one_iff.mp, iff_true_right, mem_top
-/
theorem bot_eq_top_of_finrank_adjoin_eq_one (h : forall x : E, finrank F F⟮x⟯ = 1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  ext y
  rw [iff_true_right IntermediateField.mem_top]
  exact finrank_adjoin_simple_eq_one_iff.mp (h y)

/--
theorem `subsingleton_of_rank_adjoin_eq_one` / 定理 `subsingleton_of_rank_adjoin_eq_one`

English:
theorem subsingleton_of_rank_adjoin_eq_one
  given: (h : forall x : E, Module.rank F F⟮x⟯ = 1)
  proof: subsingleton_of_bot_eq_top (bot_eq_top_of_rank_adjoin_eq_one h)

中文:
定理 subsingleton_of_rank_adjoin_eq_one
  条件: (h : 对任意 x : E, Module.rank F F⟮x⟯ = 1)
  证明: subsingleton_of_bot_eq_top (bot_eq_top_of_rank_adjoin_eq_one h)

Depends on / 依赖: bot_eq_top_of_rank_adjoin_eq_one, subsingleton_of_bot_eq_top
-/
theorem subsingleton_of_rank_adjoin_eq_one (h : forall x : E, Module.rank F F⟮x⟯ = 1) :
    Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_rank_adjoin_eq_one h)

/--
theorem `subsingleton_of_finrank_adjoin_eq_one` / 定理 `subsingleton_of_finrank_adjoin_eq_one`

English:
theorem subsingleton_of_finrank_adjoin_eq_one
  given: (h : forall x : E, finrank F F⟮x⟯ = 1)
  proof: subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_eq_one h)

中文:
定理 subsingleton_of_finrank_adjoin_eq_one
  条件: (h : 对任意 x : E, finrank F F⟮x⟯ = 1)
  证明: subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_eq_one h)

Depends on / 依赖: bot_eq_top_of_finrank_adjoin_eq_one, subsingleton_of_bot_eq_top
-/
theorem subsingleton_of_finrank_adjoin_eq_one (h : forall x : E, finrank F F⟮x⟯ = 1) :
    Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_eq_one h)

/--
theorem `bot_eq_top_of_finrank_adjoin_le_one` / 定理 `bot_eq_top_of_finrank_adjoin_le_one`

English:
theorem bot_eq_top_of_finrank_adjoin_le_one
  statement: [FiniteDimensional F E]
  proof: by
  apply bot_eq_top_of_finrank_adjoin_eq_one
  exact fun x => by linarith [h x, show 0 < finrank F F⟮x⟯ from finrank_pos]

中文:
定理 bot_eq_top_of_finrank_adjoin_le_one
  结论: [FiniteDimensional F E]
  证明: by
  apply bot_eq_top_of_finrank_adjoin_eq_one
  exact fun x => by linarith [h x, show 0 < finrank F F⟮x⟯ from finrank_pos]

Depends on / 依赖: bot_eq_top_of_finrank_adjoin_eq_one, finrank, finrank_pos
-/
theorem bot_eq_top_of_finrank_adjoin_le_one [FiniteDimensional F E]
    (h : forall x : E, finrank F F⟮x⟯ <= 1) : (⊥ : IntermediateField F E) = ⊤ := by
  apply bot_eq_top_of_finrank_adjoin_eq_one
  exact fun x => by linarith [h x, show 0 < finrank F F⟮x⟯ from finrank_pos]

/--
theorem `subsingleton_of_finrank_adjoin_le_one` / 定理 `subsingleton_of_finrank_adjoin_le_one`

English:
theorem subsingleton_of_finrank_adjoin_le_one
  statement: [FiniteDimensional F E]
  proof: subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_le_one h)

中文:
定理 subsingleton_of_finrank_adjoin_le_one
  结论: [FiniteDimensional F E]
  证明: subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_le_one h)

Depends on / 依赖: bot_eq_top_of_finrank_adjoin_le_one, subsingleton_of_bot_eq_top
-/
theorem subsingleton_of_finrank_adjoin_le_one [FiniteDimensional F E]
    (h : forall x : E, finrank F F⟮x⟯ <= 1) : Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_le_one h)

end AdjoinRank

end AdjoinIntermediateFieldLattice

section AdjoinIntegralElement

universe u

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {α : E}
variable {K : Type u} [Field K] [Algebra F K]

/--
theorem `minpoly_gen` / 定理 `minpoly_gen`

English:
theorem minpoly_gen
  given: (α : E)
  proof: by
  rw [← minpoly.algebraMap_eq (algebraMap F⟮α⟯ E).injective]; rw [AdjoinSimple.algebraMap_gen]

中文:
定理 minpoly_gen
  条件: (α : E)
  证明: by
  rw [← minpoly.algebraMap_eq (algebraMap F⟮α⟯ E).injective]; rw [AdjoinSimple.algebraMap_gen]

Depends on / 依赖: AdjoinSimple, AdjoinSimple.algebraMap_gen, algebraMap, algebraMap_eq, algebraMap_gen, injective, minpoly, minpoly.algebraMap_eq
-/
theorem minpoly_gen (α : E) :
    minpoly F (AdjoinSimple.gen F α) = minpoly F α := by
  rw [← minpoly.algebraMap_eq (algebraMap F⟮α⟯ E).injective]; rw [AdjoinSimple.algebraMap_gen]

/--
theorem `aeval_gen_minpoly` / 定理 `aeval_gen_minpoly`

English:
theorem aeval_gen_minpoly
  given: (α : E)
  statement: aeval (AdjoinSimple.gen F α) (minpoly F α) = 0
  proof: by
  ext
  convert! minpoly.aeval F α
  conv in aeval α => rw [← AdjoinSimple.algebraMap_gen F α]
  exact (aeval_algebraMap_apply E (AdjoinSimple.gen F α) _).symm

中文:
定理 aeval_gen_minpoly
  条件: (α : E)
  结论: aeval (AdjoinSimple.gen F α) (minpoly F α) = 0
  证明: by
  ext
  convert! minpoly.aeval F α
  conv in aeval α => rw [← AdjoinSimple.algebraMap_gen F α]
  exact (aeval_algebraMap_apply E (AdjoinSimple.gen F α) _).symm

Depends on / 依赖: AdjoinSimple, AdjoinSimple.algebraMap_gen, AdjoinSimple.gen, aeval_algebraMap_apply, algebraMap_gen, convert, minpoly, minpoly.aeval
-/
theorem aeval_gen_minpoly (α : E) : aeval (AdjoinSimple.gen F α) (minpoly F α) = 0 := by
  ext
  convert! minpoly.aeval F α
  conv in aeval α => rw [← AdjoinSimple.algebraMap_gen F α]
  exact (aeval_algebraMap_apply E (AdjoinSimple.gen F α) _).symm

/-- algebra isomorphism between `AdjoinRoot` and `F⟮α⟯` -/
@[stacks 09G1 "Algebraic case"]
/--
Definition of `adjoinRootEquivAdjoin` / `adjoinRootEquivAdjoin` 的定义

English:
definition adjoinRootEquivAdjoin
  signature: (h : IsIntegral F α)
  body: AlgEquiv.ofBijective
    (AdjoinRoot.liftAlgHom (minpoly F α) _ (AdjoinSimple.gen F α) (aeval_gen_minpoly F α))
    (by
      set f := AdjoinRoot.lift _ _ (aeval_gen_minpoly F α :)
      have := Fact.mk (minpoly.irreducible h)
      constructor
      · exact RingHom.injective f
      · suffices F⟮α⟯

中文:
定义 adjoinRootEquivAdjoin
  签名: (h : Is整数egral F α)
  定义体: AlgEquiv.ofBijective
    (AdjoinRoot.liftAlgHom (minpoly F α) _ (AdjoinSimple.gen F α) (aeval_gen_minpoly F α))
    (by
      set f := AdjoinRoot.lift _ _ (aeval_gen_minpoly F α :)
      have := Fact.mk (minpoly.irreducible h)
      constructor
      · exact RingHom.injective f
      · suffices F⟮α⟯

Depends on / 依赖: AdjoinRoot, AdjoinRoot.lift, AdjoinRoot.liftAlgHom, AdjoinSimple, AdjoinSimple.gen, AlgEquiv, AlgEquiv.ofBijective, Fact.mk, RingHom, RingHom.fieldRange, RingHom.injective, Set.union_subset, Subfield, Subfield.closure_le.mpr, Subtype, Subtype.ext, Subtype.mem, aeval_gen_minpoly, closure_le, fieldRange
-/
noncomputable def adjoinRootEquivAdjoin (h : IsIntegral F α) :
    AdjoinRoot (minpoly F α) ≃ₐ[F] F⟮α⟯ :=
  AlgEquiv.ofBijective
    (AdjoinRoot.liftAlgHom (minpoly F α) _ (AdjoinSimple.gen F α) (aeval_gen_minpoly F α))
    (by
      set f := AdjoinRoot.lift _ _ (aeval_gen_minpoly F α :)
      have := Fact.mk (minpoly.irreducible h)
      constructor
      · exact RingHom.injective f
      · suffices F⟮α⟯.toSubfield <= RingHom.fieldRange (F⟮α⟯.toSubfield.subtype.comp f) by
          intro x
          obtain ⟨y, hy⟩ := this (Subtype.mem x)
          exact ⟨y, Subtype.ext hy⟩
        refine Subfield.closure_le.mpr (Set.union_subset (fun x hx => ?_) ?_)
        · obtain ⟨y, hy⟩ := hx
          refine ⟨y, ?_⟩
          rw [RingHom.comp_apply]
          dsimp only [coe_type_toSubfield]
          rw [AdjoinRoot.lift_of (aeval_gen_minpoly F α)]
          exact hy
        · refine Set.singleton_subset_iff.mpr ⟨AdjoinRoot.root (minpoly F α), ?_⟩
          rw [RingHom.comp_apply]
          dsimp only [coe_type_toSubfield]
          rw [AdjoinRoot.lift_root (aeval_gen_minpoly F α)]
          rfl)

/--
theorem `adjoinRootEquivAdjoin_apply_root` / 定理 `adjoinRootEquivAdjoin_apply_root`

English:
theorem adjoinRootEquivAdjoin_apply_root
  given: (h : IsIntegral F α)
  proof: AdjoinRoot.lift_root (aeval_gen_minpoly F α)

@[simp]

中文:
定理 adjoinRootEquivAdjoin_apply_root
  条件: (h : Is整数egral F α)
  证明: AdjoinRoot.lift_root (aeval_gen_minpoly F α)

@[simp]

Depends on / 依赖: AdjoinRoot, AdjoinRoot.lift_root, aeval_gen_minpoly, lift_root
-/
theorem adjoinRootEquivAdjoin_apply_root (h : IsIntegral F α) :
    adjoinRootEquivAdjoin F h (AdjoinRoot.root (minpoly F α)) = AdjoinSimple.gen F α :=
  AdjoinRoot.lift_root (aeval_gen_minpoly F α)

@[simp]
/--
theorem `adjoinRootEquivAdjoin_symm_apply_gen` / 定理 `adjoinRootEquivAdjoin_symm_apply_gen`

English:
theorem adjoinRootEquivAdjoin_symm_apply_gen
  given: (h : IsIntegral F α)
  proof: by
  rw [AlgEquiv.symm_apply_eq]; rw [adjoinRootEquivAdjoin_apply_root]

中文:
定理 adjoinRootEquivAdjoin_symm_apply_gen
  条件: (h : Is整数egral F α)
  证明: by
  rw [AlgEquiv.symm_apply_eq]; rw [adjoinRootEquivAdjoin_apply_root]

Depends on / 依赖: AlgEquiv, AlgEquiv.symm_apply_eq, adjoinRootEquivAdjoin_apply_root, symm_apply_eq
-/
theorem adjoinRootEquivAdjoin_symm_apply_gen (h : IsIntegral F α) :
    (adjoinRootEquivAdjoin F h).symm (AdjoinSimple.gen F α) = AdjoinRoot.root (minpoly F α) := by
  rw [AlgEquiv.symm_apply_eq]; rw [adjoinRootEquivAdjoin_apply_root]

/--
theorem `adjoin_root_eq_top` / 定理 `adjoin_root_eq_top`

English:
theorem adjoin_root_eq_top
  given: (p : K[X]) [Fact (Irreducible p)]
  statement: K⟮AdjoinRoot.root p⟯ = ⊤
  proof: (eq_adjoin_of_eq_algebra_adjoin K _ ⊤ (AdjoinRoot.adjoinRoot_eq_top (f := p)).symm).symm

中文:
定理 adjoin_root_eq_top
  条件: (p : K[X]) [Fact (Irreducible p)]
  结论: K⟮AdjoinRoot.root p⟯ = ⊤
  证明: (eq_adjoin_of_eq_algebra_adjoin K _ ⊤ (AdjoinRoot.adjoinRoot_eq_top (f := p)).symm).symm

Depends on / 依赖: AdjoinRoot, AdjoinRoot.adjoinRoot_eq_top, adjoinRoot_eq_top, eq_adjoin_of_eq_algebra_adjoin
-/
theorem adjoin_root_eq_top (p : K[X]) [Fact (Irreducible p)] : K⟮AdjoinRoot.root p⟯ = ⊤ :=
  (eq_adjoin_of_eq_algebra_adjoin K _ ⊤ (AdjoinRoot.adjoinRoot_eq_top (f := p)).symm).symm

section PowerBasis

variable {L : Type*} [Field L] [Algebra K L]

/--
Definition of `powerBasisAux` / `powerBasisAux` 的定义

English:
definition powerBasisAux
  signature: {x : L} (hx : IsIntegral K x)
  body: (AdjoinRoot.powerBasis (minpoly.ne_zero hx)).basis
.map (adjoinRootEquivAdjoin K hx).toLinearEquiv
.reindex (finCongr rfl)

中文:
定义 powerBasisAux
  签名: {x : L} (hx : Is整数egral K x)
  定义体: (AdjoinRoot.powerBasis (minpoly.ne_zero hx)).basis
.map (adjoinRootEquivAdjoin K hx).toLinearEquiv
.reindex (finCongr rfl)

Depends on / 依赖: AdjoinRoot, AdjoinRoot.powerBasis, adjoinRootEquivAdjoin, finCongr, minpoly, minpoly.ne_zero, ne_zero, powerBasis, reindex, toLinearEquiv
-/
noncomputable def powerBasisAux {x : L} (hx : IsIntegral K x) :
    Basis (Fin (minpoly K x).natDegree) K K⟮x⟯ :=
  (AdjoinRoot.powerBasis (minpoly.ne_zero hx)).basis
.map (adjoinRootEquivAdjoin K hx).toLinearEquiv
.reindex (finCongr rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
@[simps]
/--
Definition of `adjoin.powerBasis` / `adjoin.powerBasis` 的定义

English:
definition adjoin.powerBasis
  signature: {x : L} (hx : IsIntegral K x)
  body: AdjoinSimple.gen K x
  dim := (minpoly K x).natDegree
  basis := powerBasisAux hx
  basis_eq_pow i := by
    rw [powerBasisAux]; rw [Basis.reindex_apply]; rw [Basis.map_apply]; rw [PowerBasis.basis_eq_pow]; rw [finCongr_symm]; rw [finCongr_apply]; rw [Fin.cast_eq_self]; rw [AlgEquiv.toLinearEquiv_ap

中文:
定义 adjoin.powerBasis
  签名: {x : L} (hx : Is整数egral K x)
  定义体: AdjoinSimple.gen K x
  dim := (minpoly K x).natDegree
  basis := powerBasisAux hx
  basis_eq_pow i := by
    rw [powerBasisAux]; rw [Basis.reindex_apply]; rw [Basis.map_apply]; rw [PowerBasis.basis_eq_pow]; rw [finCongr_symm]; rw [finCongr_apply]; rw [Fin.cast_eq_self]; rw [AlgEquiv.toLinearEquiv_ap

Depends on / 依赖: AdjoinSimple, AdjoinSimple.gen
-/
noncomputable def adjoin.powerBasis {x : L} (hx : IsIntegral K x) : PowerBasis K K⟮x⟯ where
  gen := AdjoinSimple.gen K x
  dim := (minpoly K x).natDegree
  basis := powerBasisAux hx
  basis_eq_pow i := by
    rw [powerBasisAux]; rw [Basis.reindex_apply]; rw [Basis.map_apply]; rw [PowerBasis.basis_eq_pow]; rw [finCongr_symm]; rw [finCongr_apply]; rw [Fin.cast_eq_self]; rw [AlgEquiv.toLinearEquiv_apply]; rw [map_pow]; rw [AdjoinRoot.powerBasis_gen]; rw [adjoinRootEquivAdjoin_apply_root]

/--
theorem `adjoin.finiteDimensional` / 定理 `adjoin.finiteDimensional`

English:
theorem adjoin.finiteDimensional
  given: {x : L} (hx : IsIntegral K x)
  statement: FiniteDimensional K K⟮x⟯
  proof: (adjoin.powerBasis hx).finite

中文:
定理 adjoin.finiteDimensional
  条件: {x : L} (hx : Is整数egral K x)
  结论: FiniteDimensional K K⟮x⟯
  证明: (adjoin.powerBasis hx).finite

Depends on / 依赖: adjoin, adjoin.powerBasis, finite, powerBasis
-/
theorem adjoin.finiteDimensional {x : L} (hx : IsIntegral K x) : FiniteDimensional K K⟮x⟯ :=
  (adjoin.powerBasis hx).finite

/--
theorem `isAlgebraic_adjoin_simple` / 定理 `isAlgebraic_adjoin_simple`

English:
theorem isAlgebraic_adjoin_simple
  given: {x : L} (hx : IsIntegral K x)
  statement: Algebra.IsAlgebraic K K⟮x⟯
  proof: have := adjoin.finiteDimensional hx; Algebra.IsAlgebraic.of_finite K K⟮x⟯

中文:
定理 isAlgebraic_adjoin_simple
  条件: {x : L} (hx : Is整数egral K x)
  结论: Algebra.IsAlgebraic K K⟮x⟯
  证明: have := adjoin.finiteDimensional hx; Algebra.IsAlgebraic.of_finite K K⟮x⟯

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.of_finite, IsAlgebraic, adjoin, adjoin.finiteDimensional, finiteDimensional, of_finite
-/
theorem isAlgebraic_adjoin_simple {x : L} (hx : IsIntegral K x) : Algebra.IsAlgebraic K K⟮x⟯ :=
  have := adjoin.finiteDimensional hx; Algebra.IsAlgebraic.of_finite K K⟮x⟯

/-- If `x` is an algebraic element of field `K`, then its minimal polynomial has degree
`[K(x) : K]`. -/
@[stacks 09GN]
/--
theorem `adjoin.finrank` / 定理 `adjoin.finrank`

English:
theorem adjoin.finrank
  given: {x : L} (hx : IsIntegral K x)
  proof: by
  rw [PowerBasis.finrank (adjoin.powerBasis hx :)]
  rfl

中文:
定理 adjoin.finrank
  条件: {x : L} (hx : Is整数egral K x)
  证明: by
  rw [PowerBasis.finrank (adjoin.powerBasis hx :)]
  rfl

Depends on / 依赖: PowerBasis, PowerBasis.finrank, adjoin, adjoin.powerBasis, finrank, powerBasis
-/
theorem adjoin.finrank {x : L} (hx : IsIntegral K x) :
    Module.finrank K K⟮x⟯ = (minpoly K x).natDegree := by
  rw [PowerBasis.finrank (adjoin.powerBasis hx :)]
  rfl

/--
theorem `adjoin_eq_top_of_adjoin_eq_top` / 定理 `adjoin_eq_top_of_adjoin_eq_top`

English:
theorem adjoin_eq_top_of_adjoin_eq_top
  statement: [Algebra E K] [IsScalarTower F E K]
  proof: restrictScalars_injective F by
    rw [restrictScalars_top]; rw [← top_le_iff]; rw [← hprim]; rw [adjoin_le_iff]; rw [coe_restrictScalars]; rw [← adjoin_le_iff]

中文:
定理 adjoin_eq_top_of_adjoin_eq_top
  结论: [Algebra E K] [IsScalarTower F E K]
  证明: restrictScalars_injective F by
    rw [restrictScalars_top]; rw [← top_le_iff]; rw [← hprim]; rw [adjoin_le_iff]; rw [coe_restrictScalars]; rw [← adjoin_le_iff]

Depends on / 依赖: adjoin_le_iff, coe_restrictScalars, restrictScalars_injective, restrictScalars_top, top_le_iff
-/
theorem adjoin_eq_top_of_adjoin_eq_top [Algebra E K] [IsScalarTower F E K]
    {S : Set K} (hprim : adjoin F S = ⊤) : adjoin E S = ⊤ :=
restrictScalars_injective F by
    rw [restrictScalars_top]; rw [← top_le_iff]; rw [← hprim]; rw [adjoin_le_iff]; rw [coe_restrictScalars]; rw [← adjoin_le_iff]

/--
theorem `adjoin_minpoly_coeff_of_exists_primitive_element` / 定理 `adjoin_minpoly_coeff_of_exists_primitive_element`

English:
theorem adjoin_minpoly_coeff_of_exists_primitive_element
  proof: by
  set g := (minpoly K α).map (algebraMap K E)
  set K' : IntermediateField F E := adjoin F g.coeffs
  have hsub : K' <= K := by
    refine adjoin_le_iff.mpr fun x => ?_
    rw [Finset.mem_coe]; rw [mem_coeffs_iff]
    rintro ⟨n, -, rfl⟩
    rw [coeff_map]
    apply Subtype.mem
  have dvd_g : minp

中文:
定理 adjoin_minpoly_coeff_of_exists_primitive_element
  证明: by
  set g := (minpoly K α).map (algebraMap K E)
  set K' : IntermediateField F E := adjoin F g.coeffs
  have hsub : K' <= K := by
    refine adjoin_le_iff.mpr fun x => ?_
    rw [Finset.mem_coe]; rw [mem_coeffs_iff]
    rintro ⟨n, -, rfl⟩
    rw [coeff_map]
    apply Subtype.mem
  have dvd_g : minp

Depends on / 依赖: Finset, Finset.mem_coe, IntermediateField, Subtype, Subtype.mem, adjoin, adjoin_le_iff, adjoin_le_iff.mpr, aeval_def, algebraMap, coeff_map, coeffs, dvd_g, eval_map_algebraMap, finrank_eq, g.coeffs, g.map_toSubring, g.toSubring, map_toSubring, mem_coe
-/
theorem adjoin_minpoly_coeff_of_exists_primitive_element
    [FiniteDimensional F E] (hprim : adjoin F {α} = ⊤) (K : IntermediateField F E) :
    adjoin F ((minpoly K α).map (algebraMap K E)).coeffs = K := by
  set g := (minpoly K α).map (algebraMap K E)
  set K' : IntermediateField F E := adjoin F g.coeffs
  have hsub : K' <= K := by
    refine adjoin_le_iff.mpr fun x => ?_
    rw [Finset.mem_coe]; rw [mem_coeffs_iff]
    rintro ⟨n, -, rfl⟩
    rw [coeff_map]
    apply Subtype.mem
  have dvd_g : minpoly K' α ∣ g.toSubring K'.toSubring (subset_adjoin F _) := by
    apply minpoly.dvd
    rw [aeval_def]; rw [eval₂_eq_eval_map]
    erw [g.map_toSubring K'.toSubring]
    rw [eval_map_algebraMap]
    exact minpoly.aeval K α
  have finrank_eq : forall K : IntermediateField F E, finrank K E = natDegree (minpoly K α) := by
    intro K
    have := adjoin.finrank (.of_finite K α)
    rw [adjoin_eq_top_of_adjoin_eq_top F hprim] at this
    simp_all
  refine eq_of_le_of_finrank_le' hsub ?_
  simp_rw [finrank_eq]
  convert!
    natDegree_le_of_dvd dvd_g
      ((g.monic_toSubring _ _).mpr <| (minpoly.monic <| .of_finite K α).map _).ne_zero using 1
  rw [natDegree_toSubring]; rw [natDegree_map]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite F (⊥ : IntermediateField F E)
  body: Subalgebra.finite_bot

中文:
实例 :
  签名: Module.Finite F (⊥ : 整数ermediateField F E)
  定义体: Subalgebra.finite_bot

Depends on / 依赖: Subalgebra, Subalgebra.finite_bot, finite_bot
-/
instance : Module.Finite F (⊥ : IntermediateField F E) := Subalgebra.finite_bot

variable {F} in
/--
theorem `exists_lt_finrank_of_infinite_dimensional` / 定理 `exists_lt_finrank_of_infinite_dimensional`

English:
theorem exists_lt_finrank_of_infinite_dimensional
  proof: by
  induction n with
  | zero => exact ⟨⊥, Subalgebra.finite_bot, finrank_pos⟩
  | succ n ih =>
    obtain ⟨L, fin, hn⟩ := ih
    obtain ⟨x, hx⟩ : exists x : E, x ∉ L := by
      contrapose! hnfd
      rw [show L = ⊤ from eq_top_iff.2 fun x _ => hnfd x] at fin
      exact topEquiv.toLinearEquiv.fin

中文:
定理 exists_lt_finrank_of_infinite_dimensional
  证明: by
  induction n with
  | zero => exact ⟨⊥, Subalgebra.finite_bot, finrank_pos⟩
  | succ n ih =>
    obtain ⟨L, fin, hn⟩ := ih
    obtain ⟨x, hx⟩ : exists x : E, x ∉ L := by
      contrapose! hnfd
      rw [show L = ⊤ from eq_top_iff.2 fun x _ => hnfd x] at fin
      exact topEquiv.toLinearEquiv.fin

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, Subalgebra, Subalgebra.finite_bot, adjoin, adjoin.finiteDimensional, contrapose, eq_of_le_of_finrank_le, eq_top_iff, finiteDimensional, finite_bot, finrank_pos, isIntegral, le_sup_left, not_lt, toLinearEquiv, topEquiv, topEquiv.toLinearEquiv.finiteDimensional
-/
theorem exists_lt_finrank_of_infinite_dimensional
    [Algebra.IsAlgebraic F E] (hnfd : ¬ FiniteDimensional F E) (n : Nat) :
    exists L : IntermediateField F E, FiniteDimensional F L ∧ n < finrank F L := by
  induction n with
  | zero => exact ⟨⊥, Subalgebra.finite_bot, finrank_pos⟩
  | succ n ih =>
    obtain ⟨L, fin, hn⟩ := ih
    obtain ⟨x, hx⟩ : exists x : E, x ∉ L := by
      contrapose! hnfd
      rw [show L = ⊤ from eq_top_iff.2 fun x _ => hnfd x] at fin
      exact topEquiv.toLinearEquiv.finiteDimensional
    let L' := L ⊔ F⟮x⟯
    have := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
    refine ⟨L', inferInstance, by_contra fun h => ?_⟩
    have h1 : L = L' := eq_of_le_of_finrank_le le_sup_left ((not_lt.1 h).trans hn)
    have h2 : F⟮x⟯ <= L' := le_sup_right
exact hx (h1.symm ▸ h2) mem_adjoin_simple_self F x

/--
theorem `_root_.minpoly.degree_dvd` / 定理 `_root_.minpoly.degree_dvd`

English:
theorem _root_.minpoly.degree_dvd
  given: {x : L} (hx : IsIntegral K x)
  proof: by
  rw [dvd_iff_exists_eq_mul_left]; rw [← IntermediateField.adjoin.finrank hx]
  use finrank K⟮x⟯ L
  rw [mul_comm]; rw [finrank_mul_finrank]

中文:
定理 _root_.minpoly.degree_dvd
  条件: {x : L} (hx : Is整数egral K x)
  证明: by
  rw [dvd_iff_exists_eq_mul_left]; rw [← IntermediateField.adjoin.finrank hx]
  use finrank K⟮x⟯ L
  rw [mul_comm]; rw [finrank_mul_finrank]

Depends on / 依赖: IntermediateField, IntermediateField.adjoin.finrank, adjoin, dvd_iff_exists_eq_mul_left, finrank, finrank_mul_finrank, mul_comm
-/
theorem _root_.minpoly.degree_dvd {x : L} (hx : IsIntegral K x) :
    (minpoly K x).natDegree ∣ finrank K L := by
  rw [dvd_iff_exists_eq_mul_left]; rw [← IntermediateField.adjoin.finrank hx]
  use finrank K⟮x⟯ L
  rw [mul_comm]; rw [finrank_mul_finrank]

/--
theorem `_root_.Polynomial.Irreducible.natDegree_dvd_finrank` / 定理 `_root_.Polynomial.Irreducible.natDegree_dvd_finrank`

English:
theorem _root_.Polynomial.Irreducible.natDegree_dvd_finrank
  statement: {f : K[X]} (hi : Irreducible f)
  proof: by
  have := hi.degree_pos.ne'
  rw [← f.degree_map (algebraMap K L)] at this
  obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero this
  rw [eval_map_algebraMap] at hx
  have key := minpoly.Irreducible.eq_minpoly hi hx
  replace hi := hi.ne_zero
  rw [key]; rw [natDegree_C_mul (leadingCoeff_ne_zero.mpr hi)]


中文:
定理 _root_.Polynomial.Irreducible.natDegree_dvd_finrank
  结论: {f : K[X]} (hi : Irreducible f)
  证明: by
  have := hi.degree_pos.ne'
  rw [← f.degree_map (algebraMap K L)] at this
  obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero this
  rw [eval_map_algebraMap] at hx
  have key := minpoly.Irreducible.eq_minpoly hi hx
  replace hi := hi.ne_zero
  rw [key]; rw [natDegree_C_mul (leadingCoeff_ne_zero.mpr hi)]


Depends on / 依赖: Irreducible, algebraMap, contrapose, degree_dvd, degree_map, degree_pos, eq_minpoly, eval_map_algebraMap, exists_eval_eq_zero, f.degree_map, hi.degree_pos.ne, hi.ne_zero, hs.exists_eval_eq_zero, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, minpoly, minpoly.Irreducible.eq_minpoly, minpoly.degree_dvd, minpoly.ne_zero_iff, mul_zero
-/
theorem _root_.Polynomial.Irreducible.natDegree_dvd_finrank {f : K[X]} (hi : Irreducible f)
    (hs : (f.map (algebraMap K L)).Splits) : f.natDegree ∣ finrank K L := by
  have := hi.degree_pos.ne'
  rw [← f.degree_map (algebraMap K L)] at this
  obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero this
  rw [eval_map_algebraMap] at hx
  have key := minpoly.Irreducible.eq_minpoly hi hx
  replace hi := hi.ne_zero
  rw [key]; rw [natDegree_C_mul (leadingCoeff_ne_zero.mpr hi)]
  apply minpoly.degree_dvd
  rw [← minpoly.ne_zero_iff]
  contrapose hi
  rwa [hi, mul_zero] at key

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.IsAlgebraic K (⊥ : IntermediateField K L)
  body: by
    intro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := hx
    exact isAlgebraic_algebraMap c

中文:
实例 :
  签名: Algebra.IsAlgebraic K (⊥ : 整数ermediateField K L)
  定义体: by
    intro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := hx
    exact isAlgebraic_algebraMap c

Depends on / 依赖: isAlgebraic_algebraMap
-/
instance : Algebra.IsAlgebraic K (⊥ : IntermediateField K L) where
  isAlgebraic := by
    intro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := hx
    exact isAlgebraic_algebraMap c

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.IsAlgebraic (⊤ : IntermediateField K L) L
  body: by
    intro x
    let xt : (⊤ : IntermediateField K L) := ⟨x, mem_top⟩
    exact isAlgebraic_algebraMap xt

中文:
实例 :
  签名: Algebra.IsAlgebraic (⊤ : 整数ermediateField K L) L
  定义体: by
    intro x
    let xt : (⊤ : IntermediateField K L) := ⟨x, mem_top⟩
    exact isAlgebraic_algebraMap xt

Depends on / 依赖: IntermediateField, isAlgebraic_algebraMap, mem_top
-/
instance : Algebra.IsAlgebraic (⊤ : IntermediateField K L) L where
  isAlgebraic := by
    intro x
    let xt : (⊤ : IntermediateField K L) := ⟨x, mem_top⟩
    exact isAlgebraic_algebraMap xt

-- TODO: generalize to `Sort`
/--
theorem `isAlgebraic_iSup` / 定理 `isAlgebraic_iSup`

English:
theorem isAlgebraic_iSup
  statement: {ι : Type*} {t : ι -> IntermediateField K L}
  proof: by
  constructor
  rintro ⟨x, hx⟩
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr' hx
  rw [isAlgebraic_iff]; rw [Subtype.coe_mk]; rw [← Subtype.coe_mk (p := (· in _)) x hx]; rw [← isAlgebraic_iff]
  have : forall i : Σ i, t i, FiniteDimensional K K⟮(i.2 : L)⟯ := fun ⟨i, x⟩ =>
    adjoin.finiteDimensi

中文:
定理 isAlgebraic_iSup
  结论: {ι : 类型} {t : ι -> 整数ermediateField K L}
  证明: by
  constructor
  rintro ⟨x, hx⟩
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr' hx
  rw [isAlgebraic_iff]; rw [Subtype.coe_mk]; rw [← Subtype.coe_mk (p := (· in _)) x hx]; rw [← isAlgebraic_iff]
  have : forall i : Σ i, t i, FiniteDimensional K K⟮(i.2 : L)⟯ := fun ⟨i, x⟩ =>
    adjoin.finiteDimensi

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, FiniteDimensional, IsAlgebraic, IsAlgebraic.of_finite, IsIntegral, Subtype, Subtype.coe_mk, adjoin, adjoin.finiteDimensional, coe_mk, exists_finset_of_mem_supr, finiteDimensional, isAlgebraic_iff, isIntegral, isIntegral_iff, of_finite
-/
theorem isAlgebraic_iSup {ι : Type*} {t : ι -> IntermediateField K L}
    (h : forall i, Algebra.IsAlgebraic K (t i)) :
    Algebra.IsAlgebraic K (⨆ i, t i : IntermediateField K L) := by
  constructor
  rintro ⟨x, hx⟩
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr' hx
  rw [isAlgebraic_iff]; rw [Subtype.coe_mk]; rw [← Subtype.coe_mk (p := (· in _)) x hx]; rw [← isAlgebraic_iff]
  have : forall i : Σ i, t i, FiniteDimensional K K⟮(i.2 : L)⟯ := fun ⟨i, x⟩ =>
    adjoin.finiteDimensional (isIntegral_iff.1 (Algebra.IsIntegral.isIntegral x))
  apply IsAlgebraic.of_finite

/--
theorem `isAlgebraic_adjoin` / 定理 `isAlgebraic_adjoin`

English:
theorem isAlgebraic_adjoin
  given: {S : Set L} (hS : forall x in S, IsIntegral K x)
  proof: by
  rw [← biSup_adjoin_simple]; rw [← iSup_subtype'']
  exact isAlgebraic_iSup fun x => isAlgebraic_adjoin_simple (hS x x.2)

中文:
定理 isAlgebraic_adjoin
  条件: {S : Set L} (hS : 对任意 x in S, Is整数egral K x)
  证明: by
  rw [← biSup_adjoin_simple]; rw [← iSup_subtype'']
  exact isAlgebraic_iSup fun x => isAlgebraic_adjoin_simple (hS x x.2)

Depends on / 依赖: biSup_adjoin_simple, iSup_subtype, isAlgebraic_adjoin_simple, isAlgebraic_iSup
-/
theorem isAlgebraic_adjoin {S : Set L} (hS : forall x in S, IsIntegral K x) :
    Algebra.IsAlgebraic K (adjoin K S) := by
  rw [← biSup_adjoin_simple]; rw [← iSup_subtype'']
  exact isAlgebraic_iSup fun x => isAlgebraic_adjoin_simple (hS x x.2)

/--
theorem `finiteDimensional_adjoin` / 定理 `finiteDimensional_adjoin`

English:
theorem finiteDimensional_adjoin
  given: {S : Set L} [Finite S] (hS : forall x in S, IsIntegral K x)
  proof: by
  rw [← biSup_adjoin_simple]; rw [← iSup_subtype'']
  have (x : S) := adjoin.finiteDimensional (hS x.1 x.2)
  exact finiteDimensional_iSup_of_finite

中文:
定理 finiteDimensional_adjoin
  条件: {S : Set L} [Finite S] (hS : 对任意 x in S, Is整数egral K x)
  证明: by
  rw [← biSup_adjoin_simple]; rw [← iSup_subtype'']
  have (x : S) := adjoin.finiteDimensional (hS x.1 x.2)
  exact finiteDimensional_iSup_of_finite

Depends on / 依赖: adjoin, adjoin.finiteDimensional, biSup_adjoin_simple, finiteDimensional, finiteDimensional_iSup_of_finite, iSup_subtype
-/
theorem finiteDimensional_adjoin {S : Set L} [Finite S] (hS : forall x in S, IsIntegral K x) :
    FiniteDimensional K (adjoin K S) := by
  rw [← biSup_adjoin_simple]; rw [← iSup_subtype'']
  have (x : S) := adjoin.finiteDimensional (hS x.1 x.2)
  exact finiteDimensional_iSup_of_finite

end PowerBasis

/--
Definition of `algHomAdjoinIntegralEquiv` / `algHomAdjoinIntegralEquiv` 的定义

English:
definition algHomAdjoinIntegralEquiv
  signature: (h : IsIntegral F α)
  body: (adjoin.powerBasis h).liftEquiv'.trans
    ((Equiv.refl _).subtypeEquiv fun x => by
      rw [adjoin.powerBasis_gen]; rw [minpoly_gen]; rw [Equiv.refl_apply])

中文:
定义 algHomAdjoinIntegralEquiv
  签名: (h : Is整数egral F α)
  定义体: (adjoin.powerBasis h).liftEquiv'.trans
    ((Equiv.refl _).subtypeEquiv fun x => by
      rw [adjoin.powerBasis_gen]; rw [minpoly_gen]; rw [Equiv.refl_apply])

Depends on / 依赖: Equiv.refl, Equiv.refl_apply, adjoin, adjoin.powerBasis, adjoin.powerBasis_gen, liftEquiv, minpoly_gen, powerBasis, powerBasis_gen, refl_apply, subtypeEquiv
-/
noncomputable def algHomAdjoinIntegralEquiv (h : IsIntegral F α) :
    (F⟮α⟯ ->ₐ[F] K) ≃ { x // x in (minpoly F α).aroots K } :=
  (adjoin.powerBasis h).liftEquiv'.trans
    ((Equiv.refl _).subtypeEquiv fun x => by
      rw [adjoin.powerBasis_gen]; rw [minpoly_gen]; rw [Equiv.refl_apply])

/--
lemma `algHomAdjoinIntegralEquiv_symm_apply_gen` / 引理 `algHomAdjoinIntegralEquiv_symm_apply_gen`

English:
lemma algHomAdjoinIntegralEquiv_symm_apply_gen
  statement: (h : IsIntegral F α)
  proof: (adjoin.powerBasis h).lift_gen x.val by
    rw [adjoin.powerBasis_gen]; rw [minpoly_gen]; exact (mem_aroots.mp x.2).2

中文:
引理 algHomAdjoinIntegralEquiv_symm_apply_gen
  结论: (h : Is整数egral F α)
  证明: (adjoin.powerBasis h).lift_gen x.val by
    rw [adjoin.powerBasis_gen]; rw [minpoly_gen]; exact (mem_aroots.mp x.2).2

Depends on / 依赖: adjoin, adjoin.powerBasis, adjoin.powerBasis_gen, lift_gen, mem_aroots, mem_aroots.mp, minpoly_gen, powerBasis, powerBasis_gen, x.val
-/
lemma algHomAdjoinIntegralEquiv_symm_apply_gen (h : IsIntegral F α)
    (x : { x // x in (minpoly F α).aroots K }) :
    (algHomAdjoinIntegralEquiv F h).symm x (AdjoinSimple.gen F α) = x :=
(adjoin.powerBasis h).lift_gen x.val by
    rw [adjoin.powerBasis_gen]; rw [minpoly_gen]; exact (mem_aroots.mp x.2).2

/-- Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K` -/
@[instance_reducible]
/--
Definition of `fintypeOfAlgHomAdjoinIntegral` / `fintypeOfAlgHomAdjoinIntegral` 的定义

English:
definition fintypeOfAlgHomAdjoinIntegral
  signature: (h : IsIntegral F α)
  body: PowerBasis.AlgHom.fintype (adjoin.powerBasis h)

中文:
定义 fintypeOfAlgHomAdjoinIntegral
  签名: (h : Is整数egral F α)
  定义体: PowerBasis.AlgHom.fintype (adjoin.powerBasis h)

Depends on / 依赖: AlgHom, PowerBasis, PowerBasis.AlgHom.fintype, adjoin, adjoin.powerBasis, fintype, powerBasis
-/
noncomputable def fintypeOfAlgHomAdjoinIntegral (h : IsIntegral F α) : Fintype (F⟮α⟯ ->ₐ[F] K) :=
  PowerBasis.AlgHom.fintype (adjoin.powerBasis h)

/--
theorem `card_algHom_adjoin_integral` / 定理 `card_algHom_adjoin_integral`

English:
theorem card_algHom_adjoin_integral
  statement: (h : IsIntegral F α) (h_sep : IsSeparable F α)
  proof: by
  let _ : Fintype (F⟮α⟯ ->ₐ[F] K) := fintypeOfAlgHomAdjoinIntegral F h
  rw [Nat.card_eq_fintype_card]; rw [AlgHom.card_of_powerBasis] <;>
    simp only [IsSeparable, adjoin.powerBasis_dim, adjoin.powerBasis_gen, minpoly_gen, h_splits]
  exact h_sep

中文:
定理 card_algHom_adjoin_integral
  结论: (h : Is整数egral F α) (h_sep : IsSeparable F α)
  证明: by
  let _ : Fintype (F⟮α⟯ ->ₐ[F] K) := fintypeOfAlgHomAdjoinIntegral F h
  rw [Nat.card_eq_fintype_card]; rw [AlgHom.card_of_powerBasis] <;>
    simp only [IsSeparable, adjoin.powerBasis_dim, adjoin.powerBasis_gen, minpoly_gen, h_splits]
  exact h_sep

Depends on / 依赖: AlgHom, AlgHom.card_of_powerBasis, Fintype, IsSeparable, Nat.card_eq_fintype_card, adjoin, adjoin.powerBasis_dim, adjoin.powerBasis_gen, card_eq_fintype_card, card_of_powerBasis, fintypeOfAlgHomAdjoinIntegral, h_sep, h_splits, minpoly_gen, powerBasis_dim, powerBasis_gen
-/
theorem card_algHom_adjoin_integral (h : IsIntegral F α) (h_sep : IsSeparable F α)
    (h_splits : ((minpoly F α).map (algebraMap F K)).Splits) :
    Nat.card (F⟮α⟯ ->ₐ[F] K) = (minpoly F α).natDegree := by
  let _ : Fintype (F⟮α⟯ ->ₐ[F] K) := fintypeOfAlgHomAdjoinIntegral F h
  rw [Nat.card_eq_fintype_card]; rw [AlgHom.card_of_powerBasis] <;>
    simp only [IsSeparable, adjoin.powerBasis_dim, adjoin.powerBasis_gen, minpoly_gen, h_splits]
  exact h_sep

-- Apparently `K⟮root f⟯ →+* K⟮root f⟯` is expensive to unify during instance synthesis.
open Module AdjoinRoot in
/--
theorem `_root_.Polynomial.irreducible_comp` / 定理 `_root_.Polynomial.irreducible_comp`

English:
theorem _root_.Polynomial.irreducible_comp
  statement: {f g : K[X]} (hfm : f.Monic) (hgm : g.Monic)
  proof: by
  have hf' : natDegree f != 0 :=
    fun e => not_irreducible_C (f.coeff 0) (eq_C_of_natDegree_eq_zero e ▸ hf)
  have hg' : natDegree g != 0 := by
    have := Fact.mk hf
    intro e
    apply not_irreducible_C ((g.map (algebraMap _ _)).coeff 0 - AdjoinSimple.gen K (root f))
    -- Needed to speci

中文:
定理 _root_.Polynomial.irreducible_comp
  结论: {f g : K[X]} (hfm : f.Monic) (hgm : g.Monic)
  证明: by
  have hf' : natDegree f != 0 :=
    fun e => not_irreducible_C (f.coeff 0) (eq_C_of_natDegree_eq_zero e ▸ hf)
  have hg' : natDegree g != 0 := by
    have := Fact.mk hf
    intro e
    apply not_irreducible_C ((g.map (algebraMap _ _)).coeff 0 - AdjoinSimple.gen K (root f))
    -- Needed to speci

Depends on / 依赖: AdjoinSimple, AdjoinSimple.gen, Fact.mk, algebraMap, eq_C_of_natDegree_eq_zero, f.coeff, g.map, natDegree, not_irreducible_C
-/
theorem _root_.Polynomial.irreducible_comp {f g : K[X]} (hfm : f.Monic) (hgm : g.Monic)
    (hf : Irreducible f)
    (hg : forall (E : Type u) [Field E] [Algebra K E] (x : E) (_ : minpoly K x = f),
      Irreducible (g.map (algebraMap _ _) - C (AdjoinSimple.gen K x))) :
    Irreducible (f.comp g) := by
  have hf' : natDegree f != 0 :=
    fun e => not_irreducible_C (f.coeff 0) (eq_C_of_natDegree_eq_zero e ▸ hf)
  have hg' : natDegree g != 0 := by
    have := Fact.mk hf
    intro e
    apply not_irreducible_C ((g.map (algebraMap _ _)).coeff 0 - AdjoinSimple.gen K (root f))
    -- Needed to specialize `map_sub` to avoid a timeout https://github.com/leanprover-community/mathlib4/pull/8386
    rw [RingHom.map_sub]; rw [coeff_map]; rw [← map_C]; rw [← eq_C_of_natDegree_eq_zero e]
    apply hg (AdjoinRoot f)
    rw [AdjoinRoot.minpoly_root hf.ne_zero]; rw [hfm]; rw [inv_one]; rw [map_one]; rw [mul_one]
  have H₁ : f.comp g != 0 := fun h => by simpa [hf', hg', natDegree_comp] using congr_arg natDegree h
  have H₂ : ¬ IsUnit (f.comp g) := fun h =>
    by simpa [hf', hg', natDegree_comp] using natDegree_eq_zero_of_isUnit h
  have ⟨p, hp₁, hp₂⟩ := WfDvdMonoid.exists_irreducible_factor H₂ H₁
  suffices natDegree p = natDegree f * natDegree g from (associated_of_dvd_of_natDegree_le hp₂ H₁
    (this.trans natDegree_comp.symm).ge).irreducible hp₁
  have := Fact.mk hp₁
  let Kx := AdjoinRoot p
  let := (AdjoinRoot.powerBasis hp₁.ne_zero).finite
  have key₁ : f = minpoly K (aeval (root p) g) := by
    refine minpoly.eq_of_irreducible_of_monic hf ?_ hfm
    rw [← aeval_comp]
    exact aeval_eq_zero_of_dvd_aeval_eq_zero hp₂ (AdjoinRoot.eval₂_root p)
  have key₁' : finrank K K⟮aeval (root p) g⟯ = natDegree f := by
    rw [adjoin.finrank]; rw [← key₁]
    exact IsIntegral.of_finite _ _
  have key₂ : g.map (algebraMap _ _) - C (AdjoinSimple.gen K (aeval (root p) g)) =
      minpoly K⟮aeval (root p) g⟯ (root p) :=
    minpoly.eq_of_irreducible_of_monic (hg _ _ key₁.symm) (by simp [AdjoinSimple.gen])
      (Monic.sub_of_left (hgm.map _) (degree_lt_degree (by simpa [Nat.pos_iff_ne_zero] using hg')))
  have key₂' : finrank K⟮aeval (root p) g⟯ Kx = natDegree g := by
    trans natDegree (minpoly K⟮aeval (root p) g⟯ (root p))
    · have : K⟮aeval (root p) g⟯⟮root p⟯ = ⊤ := by
        apply restrictScalars_injective K
        rw [restrictScalars_top]; rw [adjoin_adjoin_left]; rw [Set.union_comm]; rw [← adjoin_adjoin_left]; rw [adjoin_root_eq_top p]; rw [restrictScalars_adjoin]
        simp
      rw [← finrank_top']; rw [← this]; rw [adjoin.finrank]
      exact IsIntegral.of_finite _ _
    · simp [← key₂]
  have := Module.finrank_mul_finrank K K⟮aeval (root p) g⟯ Kx
  rwa [key₁', key₂', (AdjoinRoot.powerBasis hp₁.ne_zero).finrank, powerBasis_dim, eq_comm] at this

end AdjoinIntegralElement

end IntermediateField

namespace minpoly
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open AlgEquiv IntermediateField

/--
theorem `eq_of_root` / 定理 `eq_of_root`

English:
theorem eq_of_root
  statement: {x y : L} (hx : IsAlgebraic K x)
  proof: ((eq_iff_aeval_minpoly_eq_zero hx.isIntegral).mpr h_ev).symm

中文:
定理 eq_of_root
  结论: {x y : L} (hx : IsAlgebraic K x)
  证明: ((eq_iff_aeval_minpoly_eq_zero hx.isIntegral).mpr h_ev).symm

Depends on / 依赖: eq_iff_aeval_minpoly_eq_zero, h_ev, hx.isIntegral, isIntegral
-/
theorem eq_of_root {x y : L} (hx : IsAlgebraic K x)
    (h_ev : Polynomial.aeval y (minpoly K x) = 0) : minpoly K y = minpoly K x :=
  ((eq_iff_aeval_minpoly_eq_zero hx.isIntegral).mpr h_ev).symm

/--
Definition of `algEquiv` / `algEquiv` 的定义

English:
definition algEquiv
  signature: {x y : L} (hx : IsAlgebraic K x)
  body: by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, (h_mp ▸ aeval _ _)⟩
exact (adjoinRootEquivAdjoin K hx.isIntegral).symm.trans
    (AdjoinRoot.algEquivOfEq _ _ _ h_mp).trans (adjoinRootEquivAdjoin K hy.isIntegral)

中文:
定义 algEquiv
  签名: {x y : L} (hx : IsAlgebraic K x)
  定义体: by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, (h_mp ▸ aeval _ _)⟩
exact (adjoinRootEquivAdjoin K hx.isIntegral).symm.trans
    (AdjoinRoot.algEquivOfEq _ _ _ h_mp).trans (adjoinRootEquivAdjoin K hy.isIntegral)

Depends on / 依赖: AdjoinRoot, AdjoinRoot.algEquivOfEq, IsAlgebraic, adjoinRootEquivAdjoin, algEquivOfEq, h_mp, hx.isIntegral, hy.isIntegral, isIntegral, minpoly, ne_zero, symm.trans
-/
noncomputable def algEquiv {x y : L} (hx : IsAlgebraic K x)
    (h_mp : minpoly K x = minpoly K y) : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, (h_mp ▸ aeval _ _)⟩
exact (adjoinRootEquivAdjoin K hx.isIntegral).symm.trans
    (AdjoinRoot.algEquivOfEq _ _ _ h_mp).trans (adjoinRootEquivAdjoin K hy.isIntegral)

/--
theorem `algEquiv_apply` / 定理 `algEquiv_apply`

English:
theorem algEquiv_apply
  given: {x y : L} (hx : IsAlgebraic K x) (h_mp : minpoly K x = minpoly K y)
  proof: by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, (h_mp ▸ aeval _ _)⟩
  rw [algEquiv]; rw [trans_apply]; rw [← adjoinRootEquivAdjoin_apply_root K hx.isIntegral]; rw [symm_apply_apply]; rw [trans_apply]; rw [AdjoinRoot.algEquivOfEq_root]; rw [adjoinRootEquivAdjoin_apply_root K hy

中文:
定理 algEquiv_apply
  条件: {x y : L} (hx : IsAlgebraic K x) (h_mp : minpoly K x = minpoly K y)
  证明: by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, (h_mp ▸ aeval _ _)⟩
  rw [algEquiv]; rw [trans_apply]; rw [← adjoinRootEquivAdjoin_apply_root K hx.isIntegral]; rw [symm_apply_apply]; rw [trans_apply]; rw [AdjoinRoot.algEquivOfEq_root]; rw [adjoinRootEquivAdjoin_apply_root K hy

Depends on / 依赖: AdjoinRoot, AdjoinRoot.algEquivOfEq_root, IsAlgebraic, adjoinRootEquivAdjoin_apply_root, algEquiv, algEquivOfEq_root, h_mp, hx.isIntegral, hy.isIntegral, isIntegral, minpoly, ne_zero, symm_apply_apply, trans_apply
-/
theorem algEquiv_apply {x y : L} (hx : IsAlgebraic K x) (h_mp : minpoly K x = minpoly K y) :
    algEquiv hx h_mp (AdjoinSimple.gen K x) = AdjoinSimple.gen K y := by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, (h_mp ▸ aeval _ _)⟩
  rw [algEquiv]; rw [trans_apply]; rw [← adjoinRootEquivAdjoin_apply_root K hx.isIntegral]; rw [symm_apply_apply]; rw [trans_apply]; rw [AdjoinRoot.algEquivOfEq_root]; rw [adjoinRootEquivAdjoin_apply_root K hy.isIntegral]

end minpoly

namespace PowerBasis

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open IntermediateField

/--
Definition of `equivAdjoinSimple` / `equivAdjoinSimple` 的定义

English:
definition equivAdjoinSimple
  signature: (pb : PowerBasis K L)
  body: (adjoin.powerBasis pb.isIntegral_gen).equivOfMinpoly pb by
    rw [adjoin.powerBasis_gen]; rw [minpoly_gen]

@[simp]

中文:
定义 equivAdjoinSimple
  签名: (pb : PowerBasis K L)
  定义体: (adjoin.powerBasis pb.isIntegral_gen).equivOfMinpoly pb by
    rw [adjoin.powerBasis_gen]; rw [minpoly_gen]

@[simp]

Depends on / 依赖: adjoin, adjoin.powerBasis, adjoin.powerBasis_gen, equivOfMinpoly, isIntegral_gen, minpoly_gen, pb.isIntegral_gen, powerBasis, powerBasis_gen
-/
noncomputable def equivAdjoinSimple (pb : PowerBasis K L) : K⟮pb.gen⟯ ≃ₐ[K] L :=
(adjoin.powerBasis pb.isIntegral_gen).equivOfMinpoly pb by
    rw [adjoin.powerBasis_gen]; rw [minpoly_gen]

@[simp]
/--
theorem `equivAdjoinSimple_aeval` / 定理 `equivAdjoinSimple_aeval`

English:
theorem equivAdjoinSimple_aeval
  given: (pb : PowerBasis K L) (f : K[X])
  proof: equivOfMinpoly_aeval _ pb _ f

@[simp]

中文:
定理 equivAdjoinSimple_aeval
  条件: (pb : PowerBasis K L) (f : K[X])
  证明: equivOfMinpoly_aeval _ pb _ f

@[simp]

Depends on / 依赖: equivOfMinpoly_aeval
-/
theorem equivAdjoinSimple_aeval (pb : PowerBasis K L) (f : K[X]) :
    pb.equivAdjoinSimple (aeval (AdjoinSimple.gen K pb.gen) f) = aeval pb.gen f :=
  equivOfMinpoly_aeval _ pb _ f

@[simp]
/--
theorem `equivAdjoinSimple_gen` / 定理 `equivAdjoinSimple_gen`

English:
theorem equivAdjoinSimple_gen
  given: (pb : PowerBasis K L)
  proof: equivOfMinpoly_gen _ pb _

@[simp]

中文:
定理 equivAdjoinSimple_gen
  条件: (pb : PowerBasis K L)
  证明: equivOfMinpoly_gen _ pb _

@[simp]

Depends on / 依赖: equivOfMinpoly_gen
-/
theorem equivAdjoinSimple_gen (pb : PowerBasis K L) :
    pb.equivAdjoinSimple (AdjoinSimple.gen K pb.gen) = pb.gen :=
  equivOfMinpoly_gen _ pb _

@[simp]
/--
theorem `equivAdjoinSimple_symm_aeval` / 定理 `equivAdjoinSimple_symm_aeval`

English:
theorem equivAdjoinSimple_symm_aeval
  given: (pb : PowerBasis K L) (f : K[X])
  proof: by
  rw [equivAdjoinSimple]; rw [equivOfMinpoly_symm]; rw [equivOfMinpoly_aeval]; rw [adjoin.powerBasis_gen]

@[simp]

中文:
定理 equivAdjoinSimple_symm_aeval
  条件: (pb : PowerBasis K L) (f : K[X])
  证明: by
  rw [equivAdjoinSimple]; rw [equivOfMinpoly_symm]; rw [equivOfMinpoly_aeval]; rw [adjoin.powerBasis_gen]

@[simp]

Depends on / 依赖: adjoin, adjoin.powerBasis_gen, equivAdjoinSimple, equivOfMinpoly_aeval, equivOfMinpoly_symm, powerBasis_gen
-/
theorem equivAdjoinSimple_symm_aeval (pb : PowerBasis K L) (f : K[X]) :
    pb.equivAdjoinSimple.symm (aeval pb.gen f) = aeval (AdjoinSimple.gen K pb.gen) f := by
  rw [equivAdjoinSimple]; rw [equivOfMinpoly_symm]; rw [equivOfMinpoly_aeval]; rw [adjoin.powerBasis_gen]

@[simp]
/--
theorem `equivAdjoinSimple_symm_gen` / 定理 `equivAdjoinSimple_symm_gen`

English:
theorem equivAdjoinSimple_symm_gen
  given: (pb : PowerBasis K L)
  proof: by
  rw [equivAdjoinSimple]; rw [equivOfMinpoly_symm]; rw [equivOfMinpoly_gen]; rw [adjoin.powerBasis_gen]

中文:
定理 equivAdjoinSimple_symm_gen
  条件: (pb : PowerBasis K L)
  证明: by
  rw [equivAdjoinSimple]; rw [equivOfMinpoly_symm]; rw [equivOfMinpoly_gen]; rw [adjoin.powerBasis_gen]

Depends on / 依赖: adjoin, adjoin.powerBasis_gen, equivAdjoinSimple, equivOfMinpoly_gen, equivOfMinpoly_symm, powerBasis_gen
-/
theorem equivAdjoinSimple_symm_gen (pb : PowerBasis K L) :
    pb.equivAdjoinSimple.symm pb.gen = AdjoinSimple.gen K pb.gen := by
  rw [equivAdjoinSimple]; rw [equivOfMinpoly_symm]; rw [equivOfMinpoly_gen]; rw [adjoin.powerBasis_gen]

end PowerBasis

namespace IntermediateField

universe u v

open Cardinal

variable (F : Type u) [Field F]

/--
theorem `lift_cardinalMk_adjoin_le` / 定理 `lift_cardinalMk_adjoin_le`

English:
theorem lift_cardinalMk_adjoin_le
  given: {E : Type v} [Field E] [Algebra F E] (s : Set E)
  proof: by
  rw [show ↥(adjoin F s) = (adjoin F s).toSubfield from rfl]; rw [adjoin_toSubfield]
  apply (Cardinal.lift_le.mpr (Subfield.cardinalMk_closure_le_max _)).trans
  rw [lift_max]; rw [sup_le_iff]; rw [lift_aleph0]
  refine ⟨(Cardinal.lift_le.mpr ((mk_union_le _ _).trans <| add_le_max _ _)).trans ?_

中文:
定理 lift_cardinalMk_adjoin_le
  条件: {E : 类型v} [Field E] [Algebra F E] (s : Set E)
  证明: by
  rw [show ↥(adjoin F s) = (adjoin F s).toSubfield from rfl]; rw [adjoin_toSubfield]
  apply (Cardinal.lift_le.mpr (Subfield.cardinalMk_closure_le_max _)).trans
  rw [lift_max]; rw [sup_le_iff]; rw [lift_aleph0]
  refine ⟨(Cardinal.lift_le.mpr ((mk_union_le _ _).trans <| add_le_max _ _)).trans ?_

Depends on / 依赖: Cardinal, Cardinal.lift_le.mpr, Subfield, Subfield.cardinalMk_closure_le_max, add_le_max, adjoin, adjoin_toSubfield, cardinalMk_closure_le_max, le_sup_right, lift_aleph0, lift_le, lift_max, mk_range_le_lift, mk_union_le, simp_rw, sup_le_iff, toSubfield
-/
theorem lift_cardinalMk_adjoin_le {E : Type v} [Field E] [Algebra F E] (s : Set E) :
    Cardinal.lift.{u} #(adjoin F s) <= Cardinal.lift.{v} #F ⊔ Cardinal.lift.{u} #s ⊔ ℵ₀ := by
  rw [show ↥(adjoin F s) = (adjoin F s).toSubfield from rfl]; rw [adjoin_toSubfield]
  apply (Cardinal.lift_le.mpr (Subfield.cardinalMk_closure_le_max _)).trans
  rw [lift_max]; rw [sup_le_iff]; rw [lift_aleph0]
  refine ⟨(Cardinal.lift_le.mpr ((mk_union_le _ _).trans <| add_le_max _ _)).trans ?_, le_sup_right⟩
  simp_rw [lift_max, lift_aleph0]
  grw [mk_range_le_lift]

/--
theorem `cardinalMk_adjoin_le` / 定理 `cardinalMk_adjoin_le`

English:
theorem cardinalMk_adjoin_le
  given: {E : Type u} [Field E] [Algebra F E] (s : Set E)
  proof: by
  simpa using lift_cardinalMk_adjoin_le F s

中文:
定理 cardinalMk_adjoin_le
  条件: {E : 类型u} [Field E] [Algebra F E] (s : Set E)
  证明: by
  simpa using lift_cardinalMk_adjoin_le F s

Depends on / 依赖: lift_cardinalMk_adjoin_le
-/
theorem cardinalMk_adjoin_le {E : Type u} [Field E] [Algebra F E] (s : Set E) :
    #(adjoin F s) <= #F ⊔ #s ⊔ ℵ₀ := by
  simpa using lift_cardinalMk_adjoin_le F s

section AdjoinPair

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {x y : L}

/--
theorem `isAlgebraic_adjoin_pair` / 定理 `isAlgebraic_adjoin_pair`

English:
theorem isAlgebraic_adjoin_pair
  given: (hx : IsIntegral K x) (hy : IsIntegral K y)
  proof: by
  apply IntermediateField.isAlgebraic_adjoin
  simp [hx, hy]

中文:
定理 isAlgebraic_adjoin_pair
  条件: (hx : Is整数egral K x) (hy : Is整数egral K y)
  证明: by
  apply IntermediateField.isAlgebraic_adjoin
  simp [hx, hy]

Depends on / 依赖: IntermediateField, IntermediateField.isAlgebraic_adjoin, isAlgebraic_adjoin
-/
theorem isAlgebraic_adjoin_pair (hx : IsIntegral K x) (hy : IsIntegral K y) :
    Algebra.IsAlgebraic K K⟮x, y⟯ := by
  apply IntermediateField.isAlgebraic_adjoin
  simp [hx, hy]

/--
theorem `finiteDimensional_adjoin_pair` / 定理 `finiteDimensional_adjoin_pair`

English:
theorem finiteDimensional_adjoin_pair
  given: (hx : IsIntegral K x) (hy : IsIntegral K y)
  proof: by
  have := adjoin.finiteDimensional hx
  have := adjoin.finiteDimensional hy
  rw [← Set.singleton_union]; rw [adjoin_union]
  exact finiteDimensional_sup K⟮x⟯ K⟮y⟯

中文:
定理 finiteDimensional_adjoin_pair
  条件: (hx : Is整数egral K x) (hy : Is整数egral K y)
  证明: by
  have := adjoin.finiteDimensional hx
  have := adjoin.finiteDimensional hy
  rw [← Set.singleton_union]; rw [adjoin_union]
  exact finiteDimensional_sup K⟮x⟯ K⟮y⟯

Depends on / 依赖: Set.singleton_union, adjoin, adjoin.finiteDimensional, adjoin_union, finiteDimensional, finiteDimensional_sup, singleton_union
-/
theorem finiteDimensional_adjoin_pair (hx : IsIntegral K x) (hy : IsIntegral K y) :
    FiniteDimensional K K⟮x, y⟯ := by
  have := adjoin.finiteDimensional hx
  have := adjoin.finiteDimensional hy
  rw [← Set.singleton_union]; rw [adjoin_union]
  exact finiteDimensional_sup K⟮x⟯ K⟮y⟯

variable (K x y)

/--
theorem `mem_adjoin_pair_left` / 定理 `mem_adjoin_pair_left`

English:
theorem mem_adjoin_pair_left
  statement: x in K⟮x, y⟯
  proof: subset_adjoin K {x, y} (Set.mem_insert x {y})

中文:
定理 mem_adjoin_pair_left
  结论: x in K⟮x, y⟯
  证明: subset_adjoin K {x, y} (Set.mem_insert x {y})

Depends on / 依赖: Set.mem_insert, mem_insert, subset_adjoin
-/
theorem mem_adjoin_pair_left : x in K⟮x, y⟯ := subset_adjoin K {x, y} (Set.mem_insert x {y})

/--
theorem `mem_adjoin_pair_right` / 定理 `mem_adjoin_pair_right`

English:
theorem mem_adjoin_pair_right
  statement: y in K⟮x, y⟯
  proof: subset_adjoin K {x, y} (Set.mem_insert_of_mem x (Set.mem_singleton y))

中文:
定理 mem_adjoin_pair_right
  结论: y in K⟮x, y⟯
  证明: subset_adjoin K {x, y} (Set.mem_insert_of_mem x (Set.mem_singleton y))

Depends on / 依赖: Set.mem_insert_of_mem, Set.mem_singleton, mem_insert_of_mem, mem_singleton, subset_adjoin
-/
theorem mem_adjoin_pair_right : y in K⟮x, y⟯ :=
  subset_adjoin K {x, y} (Set.mem_insert_of_mem x (Set.mem_singleton y))

/--
Definition of `AdjoinPair.gen₁` / `AdjoinPair.gen₁` 的定义

English:
definition AdjoinPair.gen₁
  signature: : K⟮x, y⟯
  body: ⟨x, mem_adjoin_pair_left K x y⟩

中文:
定义 AdjoinPair.gen₁
  签名: : K⟮x, y⟯
  定义体: ⟨x, mem_adjoin_pair_left K x y⟩

Depends on / 依赖: mem_adjoin_pair_left
-/
def AdjoinPair.gen₁ : K⟮x, y⟯ := ⟨x, mem_adjoin_pair_left K x y⟩

/--
Definition of `AdjoinPair.gen₂` / `AdjoinPair.gen₂` 的定义

English:
definition AdjoinPair.gen₂
  signature: : K⟮x, y⟯
  body: ⟨y, mem_adjoin_pair_right K x y⟩

中文:
定义 AdjoinPair.gen₂
  签名: : K⟮x, y⟯
  定义体: ⟨y, mem_adjoin_pair_right K x y⟩

Depends on / 依赖: mem_adjoin_pair_right
-/
def AdjoinPair.gen₂ : K⟮x, y⟯ := ⟨y, mem_adjoin_pair_right K x y⟩

/--
theorem `AdjoinPair.algebraMap_gen₁` / 定理 `AdjoinPair.algebraMap_gen₁`

English:
theorem AdjoinPair.algebraMap_gen₁
  statement: (algebraMap (↥K⟮x, y⟯) L) (gen₁ K x y) = x
  proof: rfl

中文:
定理 AdjoinPair.algebraMap_gen₁
  结论: (algebraMap (↥K⟮x, y⟯) L) (gen₁ K x y) = x
  证明: rfl
-/
theorem AdjoinPair.algebraMap_gen₁ : (algebraMap (↥K⟮x, y⟯) L) (gen₁ K x y) = x := rfl

/--
theorem `AdjoinPair.algebraMap_gen₂` / 定理 `AdjoinPair.algebraMap_gen₂`

English:
theorem AdjoinPair.algebraMap_gen₂
  statement: (algebraMap (↥K⟮x, y⟯) L) (gen₂ K x y) = y
  proof: rfl

中文:
定理 AdjoinPair.algebraMap_gen₂
  结论: (algebraMap (↥K⟮x, y⟯) L) (gen₂ K x y) = y
  证明: rfl
-/
theorem AdjoinPair.algebraMap_gen₂ : (algebraMap (↥K⟮x, y⟯) L) (gen₂ K x y) = y := rfl

end AdjoinPair

end IntermediateField

instance (R : Type*) [CommSemiring R] (K : Type*) [Field K] [Algebra R K]
    (S : Type*) [Semiring S] [Algebra R S] [Module.Finite R S] :
    Finite (S ->ₐ[R] K) :=
  .of_equiv _ (Algebra.TensorProduct.liftEquivRight _ K _ _).symm
