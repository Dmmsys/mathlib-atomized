/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.AreComplementary
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Truncations on cochain complexes indexed by the integers.

In this file, we introduce abbreviations for the canonical truncations
`CochainComplex.truncLE`, `CochainComplex.truncGE` of cochain
complexes indexed by `ℤ`, as well as the conditions
`CochainComplex.IsStrictlyLE`, `CochainComplex.IsStrictlyGE`,
`CochainComplex.IsLE`, and `CochainComplex.IsGE`.

-/

@[expose] public section

open CategoryTheory Category Limits ComplexShape ZeroObject

namespace CochainComplex

variable {C : Type*} [Category* C]

open HomologicalComplex

section HasZeroMorphisms

variable [HasZeroMorphisms C] (K L : CochainComplex C Int) (φ : K ⟶ L) (e : K ≅ L)

section

variable [HasZeroObject C] [forall i, K.HasHomology i] [forall i, L.HasHomology i]

/--
Definition of `truncLE` / `truncLE` 的定义

English:
abbreviation truncLE
  signature: (n : Int)
  body: HomologicalComplex.truncLE K (embeddingUpIntLE n)

中文:
缩写 truncLE
  签名: (n : 整数)
  定义体: HomologicalComplex.truncLE K (embeddingUpIntLE n)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.truncLE, embeddingUpIntLE, truncLE
-/
noncomputable abbrev truncLE (n : Int) : CochainComplex C Int :=
  HomologicalComplex.truncLE K (embeddingUpIntLE n)

/--
Definition of `truncGE` / `truncGE` 的定义

English:
abbreviation truncGE
  signature: (n : Int)
  body: HomologicalComplex.truncGE K (embeddingUpIntGE n)

中文:
缩写 truncGE
  签名: (n : 整数)
  定义体: HomologicalComplex.truncGE K (embeddingUpIntGE n)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.truncGE, embeddingUpIntGE, truncGE
-/
noncomputable abbrev truncGE (n : Int) : CochainComplex C Int :=
  HomologicalComplex.truncGE K (embeddingUpIntGE n)

/--
Definition of `ιTruncLE` / `ιTruncLE` 的定义

English:
definition ιTruncLE
  signature: (n : Int)
  body: HomologicalComplex.ιTruncLE K (embeddingUpIntLE n)

中文:
定义 ιTruncLE
  签名: (n : 整数)
  定义体: HomologicalComplex.ιTruncLE K (embeddingUpIntLE n)

Depends on / 依赖: HomologicalComplex, embeddingUpIntLE
-/
noncomputable def ιTruncLE (n : Int) : K.truncLE n ⟶ K :=
  HomologicalComplex.ιTruncLE K (embeddingUpIntLE n)

/--
Definition of `πTruncGE` / `πTruncGE` 的定义

English:
definition πTruncGE
  signature: (n : Int)
  body: HomologicalComplex.πTruncGE K (embeddingUpIntGE n)

中文:
定义 πTruncGE
  签名: (n : 整数)
  定义体: HomologicalComplex.πTruncGE K (embeddingUpIntGE n)

Depends on / 依赖: BoundaryGE, HomologicalComplex, K.pOpcycles, K.truncGE, L.truncGE, XIsoOpcycles, _d_eq, _d_eq_fromOpcycles, cancel_epi, dif_neg, dif_pos, e.BoundaryGE, e.not_boundaryGE_next, embeddingUpIntGE, not_boundaryGE_next, opcyclesMap, pOpcycles, truncGE
-/
noncomputable def πTruncGE (n : Int) : K ⟶ K.truncGE n :=
  HomologicalComplex.πTruncGE K (embeddingUpIntGE n)

/--
lemma `quasiIsoAt_ιTruncLE` / 引理 `quasiIsoAt_ιTruncLE`

English:
lemma quasiIsoAt_ιTruncLE
  given: (n q : Int) (hq : q <= n)
  proof: by
  obtain ⟨k, rfl⟩ := Int.le.dest hq
  exact HomologicalComplex.quasiIsoAt_ιTruncLE (j := k) _ _ (by simp)

中文:
引理 quasiIsoAt_ιTruncLE
  条件: (n q : 整数) (hq : q <= n)
  证明: by
  obtain ⟨k, rfl⟩ := Int.le.dest hq
  exact HomologicalComplex.quasiIsoAt_ιTruncLE (j := k) _ _ (by simp)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.quasiIsoAt_, Int.le.dest, dif_pos
-/
lemma quasiIsoAt_ιTruncLE (n q : Int) (hq : q <= n) :
    QuasiIsoAt (K.ιTruncLE n) q := by
  obtain ⟨k, rfl⟩ := Int.le.dest hq
  exact HomologicalComplex.quasiIsoAt_ιTruncLE (j := k) _ _ (by simp)

/--
lemma `quasiIsoAt_πTruncGE` / 引理 `quasiIsoAt_πTruncGE`

English:
lemma quasiIsoAt_πTruncGE
  given: (n q : Int) (hq : n <= q)
  proof: by
  obtain ⟨k, rfl⟩ := Int.le.dest hq
  exact HomologicalComplex.quasiIsoAt_πTruncGE (j := k) _ _ (by simp)

中文:
引理 quasiIsoAt_πTruncGE
  条件: (n q : 整数) (hq : n <= q)
  证明: by
  obtain ⟨k, rfl⟩ := Int.le.dest hq
  exact HomologicalComplex.quasiIsoAt_πTruncGE (j := k) _ _ (by simp)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.quasiIsoAt_, Int.le.dest, dif_neg
-/
lemma quasiIsoAt_πTruncGE (n q : Int) (hq : n <= q) :
    QuasiIsoAt (K.πTruncGE n) q := by
  obtain ⟨k, rfl⟩ := Int.le.dest hq
  exact HomologicalComplex.quasiIsoAt_πTruncGE (j := k) _ _ (by simp)

instance (n : Int) : QuasiIsoAt (K.πTruncGE n) n :=
  quasiIsoAt_πTruncGE _ _ _ (by lia)

instance (n : Int) : QuasiIsoAt (K.ιTruncLE n) n :=
  quasiIsoAt_ιTruncLE _ _ _ (by lia)

section

variable {K L}

/--
Definition of `truncLEMap` / `truncLEMap` 的定义

English:
abbreviation truncLEMap
  signature: (n : Int)
  body: HomologicalComplex.truncLEMap φ (embeddingUpIntLE n)

中文:
缩写 truncLEMap
  签名: (n : 整数)
  定义体: HomologicalComplex.truncLEMap φ (embeddingUpIntLE n)

Depends on / 依赖: BoundaryGE, HomologicalComplex, HomologicalComplex.truncLEMap, Map_f_eq, Map_f_eq_opcyclesMap, e.BoundaryGE, embeddingUpIntLE, truncGE, truncLEMap
-/
noncomputable abbrev truncLEMap (n : Int) : K.truncLE n ⟶ L.truncLE n :=
  HomologicalComplex.truncLEMap φ (embeddingUpIntLE n)

/--
Definition of `truncGEMap` / `truncGEMap` 的定义

English:
abbreviation truncGEMap
  signature: (n : Int)
  body: HomologicalComplex.truncGEMap φ (embeddingUpIntGE n)

@[reassoc (attr := simp)]

中文:
缩写 truncGEMap
  签名: (n : 整数)
  定义体: HomologicalComplex.truncGEMap φ (embeddingUpIntGE n)

@[reassoc (attr := simp)]

Depends on / 依赖: BoundaryGE, HomologicalComplex, HomologicalComplex.truncGEMap, Map_f_eq, Map_f_eq_opcyclesMap, e.BoundaryGE, embeddingUpIntGE, opcyclesMap_comp, truncGE, truncGEMap
-/
noncomputable abbrev truncGEMap (n : Int) : K.truncGE n ⟶ L.truncGE n :=
  HomologicalComplex.truncGEMap φ (embeddingUpIntGE n)

@[reassoc (attr := simp)]
/--
lemma `ιTruncLE_naturality` / 引理 `ιTruncLE_naturality`

English:
lemma ιTruncLE_naturality
  given: (n : Int)
  proof: by
  apply HomologicalComplex.ιTruncLE_naturality

@[reassoc (attr := simp)]

中文:
引理 ιTruncLE_naturality
  条件: (n : 整数)
  证明: by
  apply HomologicalComplex.ιTruncLE_naturality

@[reassoc (attr := simp)]

Depends on / 依赖: HomologicalComplex
-/
lemma ιTruncLE_naturality (n : Int) :
    truncLEMap φ n ≫ L.ιTruncLE n = K.ιTruncLE n ≫ φ := by
  apply HomologicalComplex.ιTruncLE_naturality

@[reassoc (attr := simp)]
/--
lemma `πTruncGE_naturality` / 引理 `πTruncGE_naturality`

English:
lemma πTruncGE_naturality
  given: (n : Int)
  proof: by
  apply HomologicalComplex.πTruncGE_naturality

中文:
引理 πTruncGE_naturality
  条件: (n : 整数)
  证明: by
  apply HomologicalComplex.πTruncGE_naturality

Depends on / 依赖: HomologicalComplex
-/
lemma πTruncGE_naturality (n : Int) :
    K.πTruncGE n ≫ truncGEMap φ n = φ ≫ L.πTruncGE n := by
  apply HomologicalComplex.πTruncGE_naturality

end

end

/--
Definition of `IsStrictlyGE` / `IsStrictlyGE` 的定义

English:
abbreviation IsStrictlyGE
  signature: (n : Int)
  body: K.IsStrictlySupported (embeddingUpIntGE n)

中文:
缩写 IsStrictlyGE
  签名: (n : 整数)
  定义体: K.IsStrictlySupported (embeddingUpIntGE n)

Depends on / 依赖: IsStrictlySupported, K.IsStrictlySupported, embeddingUpIntGE
-/
abbrev IsStrictlyGE (n : Int) := K.IsStrictlySupported (embeddingUpIntGE n)

/--
Definition of `IsStrictlyLE` / `IsStrictlyLE` 的定义

English:
abbreviation IsStrictlyLE
  signature: (n : Int)
  body: K.IsStrictlySupported (embeddingUpIntLE n)

中文:
缩写 IsStrictlyLE
  签名: (n : 整数)
  定义体: K.IsStrictlySupported (embeddingUpIntLE n)

Depends on / 依赖: IsStrictlySupported, K.IsStrictlySupported, embeddingUpIntLE
-/
abbrev IsStrictlyLE (n : Int) := K.IsStrictlySupported (embeddingUpIntLE n)

/--
Definition of `IsGE` / `IsGE` 的定义

English:
abbreviation IsGE
  signature: (n : Int)
  body: K.IsSupported (embeddingUpIntGE n)

中文:
缩写 IsGE
  签名: (n : 整数)
  定义体: K.IsSupported (embeddingUpIntGE n)

Depends on / 依赖: IsSupported, K.IsSupported, embeddingUpIntGE
-/
abbrev IsGE (n : Int) := K.IsSupported (embeddingUpIntGE n)

/--
Definition of `IsLE` / `IsLE` 的定义

English:
abbreviation IsLE
  signature: (n : Int)
  body: K.IsSupported (embeddingUpIntLE n)

中文:
缩写 IsLE
  签名: (n : 整数)
  定义体: K.IsSupported (embeddingUpIntLE n)

Depends on / 依赖: IsSupported, K.IsSupported, embeddingUpIntLE
-/
abbrev IsLE (n : Int) := K.IsSupported (embeddingUpIntLE n)

/--
lemma `isZero_of_isStrictlyGE` / 引理 `isZero_of_isStrictlyGE`

English:
lemma isZero_of_isStrictlyGE
  given: (n i : Int) (hi : i < n := by lia) [K.IsStrictlyGE n]
  proof: isZero_X_of_isStrictlySupported K (embeddingUpIntGE n) i
    (by simpa only [notMem_range_embeddingUpIntGE_iff] using hi)

中文:
引理 isZero_of_isStrictlyGE
  条件: (n i : 整数) (hi : i < n := by lia) [K.IsStrictlyGE n]
  证明: isZero_X_of_isStrictlySupported K (embeddingUpIntGE n) i
    (by simpa only [notMem_range_embeddingUpIntGE_iff] using hi)

Depends on / 依赖: IsStrictlyGE, IsZero, K.IsStrictlyGE, embeddingUpIntGE, isZero_X_of_isStrictlySupported, notMem_range_embeddingUpIntGE_iff
-/
lemma isZero_of_isStrictlyGE (n i : Int) (hi : i < n := by lia) [K.IsStrictlyGE n] :
    IsZero (K.X i) :=
  isZero_X_of_isStrictlySupported K (embeddingUpIntGE n) i
    (by simpa only [notMem_range_embeddingUpIntGE_iff] using hi)

/--
lemma `isZero_of_isStrictlyLE` / 引理 `isZero_of_isStrictlyLE`

English:
lemma isZero_of_isStrictlyLE
  given: (n i : Int) (hi : n < i := by lia) [K.IsStrictlyLE n]
  proof: isZero_X_of_isStrictlySupported K (embeddingUpIntLE n) i
    (by simpa only [notMem_range_embeddingUpIntLE_iff] using hi)

中文:
引理 isZero_of_isStrictlyLE
  条件: (n i : 整数) (hi : n < i := by lia) [K.IsStrictlyLE n]
  证明: isZero_X_of_isStrictlySupported K (embeddingUpIntLE n) i
    (by simpa only [notMem_range_embeddingUpIntLE_iff] using hi)

Depends on / 依赖: IsStrictlyLE, IsZero, K.IsStrictlyLE, embeddingUpIntLE, isZero_X_of_isStrictlySupported, notMem_range_embeddingUpIntLE_iff
-/
lemma isZero_of_isStrictlyLE (n i : Int) (hi : n < i := by lia) [K.IsStrictlyLE n] :
    IsZero (K.X i) :=
  isZero_X_of_isStrictlySupported K (embeddingUpIntLE n) i
    (by simpa only [notMem_range_embeddingUpIntLE_iff] using hi)

/--
lemma `exactAt_of_isGE` / 引理 `exactAt_of_isGE`

English:
lemma exactAt_of_isGE
  given: (n i : Int) (hi : i < n := by lia) [K.IsGE n]
  proof: exactAt_of_isSupported K (embeddingUpIntGE n) i
    (by simpa only [notMem_range_embeddingUpIntGE_iff] using hi)

中文:
引理 exactAt_of_isGE
  条件: (n i : 整数) (hi : i < n := by lia) [K.IsGE n]
  证明: exactAt_of_isSupported K (embeddingUpIntGE n) i
    (by simpa only [notMem_range_embeddingUpIntGE_iff] using hi)

Depends on / 依赖: ExactAt, K.ExactAt, K.IsGE, embeddingUpIntGE, exactAt_of_isSupported, f_eq_iso_hom_pOpcycles_iso_inv, notMem_range_embeddingUpIntGE_iff, restrictionToTruncGE, restrictionXIso
-/
lemma exactAt_of_isGE (n i : Int) (hi : i < n := by lia) [K.IsGE n] :
    K.ExactAt i :=
  exactAt_of_isSupported K (embeddingUpIntGE n) i
    (by simpa only [notMem_range_embeddingUpIntGE_iff] using hi)

/--
lemma `exactAt_of_isLE` / 引理 `exactAt_of_isLE`

English:
lemma exactAt_of_isLE
  given: (n i : Int) (hi : n < i := by lia) [K.IsLE n]
  proof: exactAt_of_isSupported K (embeddingUpIntLE n) i
    (by simpa only [notMem_range_embeddingUpIntLE_iff] using hi)

中文:
引理 exactAt_of_isLE
  条件: (n i : 整数) (hi : n < i := by lia) [K.IsLE n]
  证明: exactAt_of_isSupported K (embeddingUpIntLE n) i
    (by simpa only [notMem_range_embeddingUpIntLE_iff] using hi)

Depends on / 依赖: ExactAt, K.ExactAt, K.IsLE, embeddingUpIntLE, exactAt_of_isSupported, f_eq_iso_hom_pOpcycles_iso_inv, notMem_range_embeddingUpIntLE_iff, restrictionToTruncGE
-/
lemma exactAt_of_isLE (n i : Int) (hi : n < i := by lia) [K.IsLE n] :
    K.ExactAt i :=
  exactAt_of_isSupported K (embeddingUpIntLE n) i
    (by simpa only [notMem_range_embeddingUpIntLE_iff] using hi)

/--
lemma `isZero_of_isGE` / 引理 `isZero_of_isGE`

English:
lemma isZero_of_isGE
  given: (n i : Int) (hi : i < n := by lia) [K.IsGE n] [K.HasHomology i]
  proof: (K.exactAt_of_isGE n i hi).isZero_homology

中文:
引理 isZero_of_isGE
  条件: (n i : 整数) (hi : i < n := by lia) [K.IsGE n] [K.HasHomology i]
  证明: (K.exactAt_of_isGE n i hi).isZero_homology

Depends on / 依赖: HasHomology, IsZero, K.HasHomology, K.IsGE, K.exactAt_of_isGE, K.homology, exactAt_of_isGE, f_eq_iso_hom_iso_inv, homology, isZero_homology, restrictionToTruncGE
-/
lemma isZero_of_isGE (n i : Int) (hi : i < n := by lia) [K.IsGE n] [K.HasHomology i] :
    IsZero (K.homology i) :=
  (K.exactAt_of_isGE n i hi).isZero_homology

/--
lemma `isZero_of_isLE` / 引理 `isZero_of_isLE`

English:
lemma isZero_of_isLE
  given: (n i : Int) (hi : n < i := by lia) [K.IsLE n] [K.HasHomology i]
  proof: (K.exactAt_of_isLE n i hi).isZero_homology

中文:
引理 isZero_of_isLE
  条件: (n i : 整数) (hi : n < i := by lia) [K.IsLE n] [K.HasHomology i]
  证明: (K.exactAt_of_isLE n i hi).isZero_homology

Depends on / 依赖: HasHomology, IsZero, K.HasHomology, K.IsLE, K.exactAt_of_isLE, K.homology, exactAt_of_isLE, homology, isZero_homology
-/
lemma isZero_of_isLE (n i : Int) (hi : n < i := by lia) [K.IsLE n] [K.HasHomology i] :
    IsZero (K.homology i) :=
  (K.exactAt_of_isLE n i hi).isZero_homology

/--
lemma `isStrictlyGE_iff` / 引理 `isStrictlyGE_iff`

English:
lemma isStrictlyGE_iff
  given: (n : Int)
  proof: by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyGE n i hi
  · intro h
    refine IsStrictlySupported.mk (fun i hi => ?_)
    rw [notMem_range_embeddingUpIntGE_iff] at hi
    exact h i hi

中文:
引理 isStrictlyGE_iff
  条件: (n : 整数)
  证明: by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyGE n i hi
  · intro h
    refine IsStrictlySupported.mk (fun i hi => ?_)
    rw [notMem_range_embeddingUpIntGE_iff] at hi
    exact h i hi

Depends on / 依赖: BoundaryGE, IsStrictlySupported, IsStrictlySupported.mk, IsZero, K.isZero_of_isStrictlyGE, Map_f_eq, Map_f_eq_opcyclesMap, _f_eq_iso_hom_iso_inv, _f_eq_iso_hom_pOpcycles_iso_inv, e.BoundaryGE, isZero_of_isStrictlyGE, notMem_range_embeddingUpIntGE_iff, restrictionToTruncGE, restrictionXIso, truncGE
-/
lemma isStrictlyGE_iff (n : Int) :
    K.IsStrictlyGE n ↔ forall (i : Int) (_ : i < n := by lia), IsZero (K.X i) := by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyGE n i hi
  · intro h
    refine IsStrictlySupported.mk (fun i hi => ?_)
    rw [notMem_range_embeddingUpIntGE_iff] at hi
    exact h i hi

/--
lemma `isStrictlyLE_iff` / 引理 `isStrictlyLE_iff`

English:
lemma isStrictlyLE_iff
  given: (n : Int)
  proof: by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyLE n i hi
  · intro h
    refine IsStrictlySupported.mk (fun i hi => ?_)
    rw [notMem_range_embeddingUpIntLE_iff] at hi
    exact h i hi

中文:
引理 isStrictlyLE_iff
  条件: (n : 整数)
  证明: by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyLE n i hi
  · intro h
    refine IsStrictlySupported.mk (fun i hi => ?_)
    rw [notMem_range_embeddingUpIntLE_iff] at hi
    exact h i hi

Depends on / 依赖: BoundaryGE, IsStrictlySupported, IsStrictlySupported.mk, K.isIso_restrictionToTruncGE, K.isZero_of_isStrictlyLE, K.restrictionToTruncGE, _f_eq_iso_hom_pOpcycles_iso_inv, e.BoundaryGE, infer_instance, isIso_restrictionToTruncGE, isZero_of_isStrictlyLE, notMem_range_embeddingUpIntLE_iff, restrictionToTruncGE
-/
lemma isStrictlyLE_iff (n : Int) :
    K.IsStrictlyLE n ↔ forall (i : Int) (_ : n < i), IsZero (K.X i) := by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyLE n i hi
  · intro h
    refine IsStrictlySupported.mk (fun i hi => ?_)
    rw [notMem_range_embeddingUpIntLE_iff] at hi
    exact h i hi

/--
lemma `isGE_iff` / 引理 `isGE_iff`

English:
lemma isGE_iff
  given: (n : Int)
  proof: by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isGE n i hi
  · intro h
    refine IsSupported.mk (fun i hi => ?_)
    rw [notMem_range_embeddingUpIntGE_iff] at hi
    exact h i hi

中文:
引理 isGE_iff
  条件: (n : 整数)
  证明: by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isGE n i hi
  · intro h
    refine IsSupported.mk (fun i hi => ?_)
    rw [notMem_range_embeddingUpIntGE_iff] at hi
    exact h i hi

Depends on / 依赖: IsSupported, IsSupported.mk, K.exactAt_of_isGE, exactAt_of_isGE, notMem_range_embeddingUpIntGE_iff
-/
lemma isGE_iff (n : Int) :
    K.IsGE n ↔ forall (i : Int) (_ : i < n), K.ExactAt i := by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isGE n i hi
  · intro h
    refine IsSupported.mk (fun i hi => ?_)
    rw [notMem_range_embeddingUpIntGE_iff] at hi
    exact h i hi

/--
lemma `isLE_iff` / 引理 `isLE_iff`

English:
lemma isLE_iff
  given: (n : Int)
  proof: by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isLE n i hi
  · intro h
    refine IsSupported.mk (fun i hi => ?_)
    rw [notMem_range_embeddingUpIntLE_iff] at hi
    exact h i hi

中文:
引理 isLE_iff
  条件: (n : 整数)
  证明: by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isLE n i hi
  · intro h
    refine IsSupported.mk (fun i hi => ?_)
    rw [notMem_range_embeddingUpIntLE_iff] at hi
    exact h i hi

Depends on / 依赖: IsSupported, IsSupported.mk, K.exactAt_of_isLE, exactAt_of_isLE, notMem_range_embeddingUpIntLE_iff
-/
lemma isLE_iff (n : Int) :
    K.IsLE n ↔ forall (i : Int) (_ : n < i), K.ExactAt i := by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isLE n i hi
  · intro h
    refine IsSupported.mk (fun i hi => ?_)
    rw [notMem_range_embeddingUpIntLE_iff] at hi
    exact h i hi

/--
lemma `isStrictlyLE_of_le` / 引理 `isStrictlyLE_of_le`

English:
lemma isStrictlyLE_of_le
  given: (p q : Int) (hpq : p <= q) [K.IsStrictlyLE p]
  proof: by
  rw [isStrictlyLE_iff]
  intro i hi
  exact K.isZero_of_isStrictlyLE p _

中文:
引理 isStrictlyLE_of_le
  条件: (p q : 整数) (hpq : p <= q) [K.IsStrictlyLE p]
  证明: by
  rw [isStrictlyLE_iff]
  intro i hi
  exact K.isZero_of_isStrictlyLE p _

Depends on / 依赖: K.isZero_of_isStrictlyLE, e.epi_liftExtend_f_iff, epi_liftExtend_f_iff, infer_instance, isStrictlyLE_iff, isZero_extend_X, isZero_of_isStrictlyLE
-/
lemma isStrictlyLE_of_le (p q : Int) (hpq : p <= q) [K.IsStrictlyLE p] :
    K.IsStrictlyLE q := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact K.isZero_of_isStrictlyLE p _

/--
lemma `isStrictlyGE_of_ge` / 引理 `isStrictlyGE_of_ge`

English:
lemma isStrictlyGE_of_ge
  given: (p q : Int) (hpq : p <= q) [K.IsStrictlyGE q]
  proof: by
  rw [isStrictlyGE_iff]
  intro i hi
  exact K.isZero_of_isStrictlyGE q _

中文:
引理 isStrictlyGE_of_ge
  条件: (p q : 整数) (hpq : p <= q) [K.IsStrictlyGE q]
  证明: by
  rw [isStrictlyGE_iff]
  intro i hi
  exact K.isZero_of_isStrictlyGE q _

Depends on / 依赖: K.isZero_of_isStrictlyGE, isStrictlyGE_iff, isZero_of_isStrictlyGE
-/
lemma isStrictlyGE_of_ge (p q : Int) (hpq : p <= q) [K.IsStrictlyGE q] :
    K.IsStrictlyGE p := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact K.isZero_of_isStrictlyGE q _

/--
lemma `isLE_of_le` / 引理 `isLE_of_le`

English:
lemma isLE_of_le
  given: (p q : Int) (hpq : p <= q) [K.IsLE p]
  proof: by
  rw [isLE_iff]
  intro i hi
  exact K.exactAt_of_isLE p _

中文:
引理 isLE_of_le
  条件: (p q : 整数) (hpq : p <= q) [K.IsLE p]
  证明: by
  rw [isLE_iff]
  intro i hi
  exact K.exactAt_of_isLE p _

Depends on / 依赖: K.exactAt_of_isLE, exactAt_of_isLE, isLE_iff
-/
lemma isLE_of_le (p q : Int) (hpq : p <= q) [K.IsLE p] :
    K.IsLE q := by
  rw [isLE_iff]
  intro i hi
  exact K.exactAt_of_isLE p _

/--
lemma `isGE_of_ge` / 引理 `isGE_of_ge`

English:
lemma isGE_of_ge
  given: (p q : Int) (hpq : p <= q) [K.IsGE q]
  proof: by
  rw [isGE_iff]
  intro i hi
  exact K.exactAt_of_isGE q _

中文:
引理 isGE_of_ge
  条件: (p q : 整数) (hpq : p <= q) [K.IsGE q]
  证明: by
  rw [isGE_iff]
  intro i hi
  exact K.exactAt_of_isGE q _

Depends on / 依赖: K.exactAt_of_isGE, exactAt_of_isGE, isGE_iff
-/
lemma isGE_of_ge (p q : Int) (hpq : p <= q) [K.IsGE q] :
    K.IsGE p := by
  rw [isGE_iff]
  intro i hi
  exact K.exactAt_of_isGE q _

section

variable {K L}

include e

/--
lemma `isStrictlyLE_of_iso` / 引理 `isStrictlyLE_of_iso`

English:
lemma isStrictlyLE_of_iso
  given: (n : Int) [K.IsStrictlyLE n]
  statement: L.IsStrictlyLE n
  proof: by
  apply isStrictlySupported_of_iso e

中文:
引理 isStrictlyLE_of_iso
  条件: (n : 整数) [K.IsStrictlyLE n]
  结论: L.IsStrictlyLE n
  证明: by
  apply isStrictlySupported_of_iso e

Depends on / 依赖: BoundaryGE, HomologicalComplex, HomologicalComplex.pOpcycles, IsZero, IsZero.iff_id_eq_zero, K.isZero_X_of_isStrictlySupported, K.truncGE, XIsoOpcycles, cancel_epi, e.BoundaryGE, eq_of_src, extendXIso, iff_id_eq_zero, isStrictlySupported_of_iso, isZero_X_of_isStr, isZero_X_of_isStrictlySupported, of_iso, pOpcycles, truncGE
-/
lemma isStrictlyLE_of_iso (n : Int) [K.IsStrictlyLE n] : L.IsStrictlyLE n := by
  apply isStrictlySupported_of_iso e

/--
lemma `isStrictlyGE_of_iso` / 引理 `isStrictlyGE_of_iso`

English:
lemma isStrictlyGE_of_iso
  given: (n : Int) [K.IsStrictlyGE n]
  statement: L.IsStrictlyGE n
  proof: by
  apply isStrictlySupported_of_iso e

中文:
引理 isStrictlyGE_of_iso
  条件: (n : 整数) [K.IsStrictlyGE n]
  结论: L.IsStrictlyGE n
  证明: by
  apply isStrictlySupported_of_iso e

Depends on / 依赖: isStrictlySupported_of_iso
-/
lemma isStrictlyGE_of_iso (n : Int) [K.IsStrictlyGE n] : L.IsStrictlyGE n := by
  apply isStrictlySupported_of_iso e

/--
lemma `isLE_of_iso` / 引理 `isLE_of_iso`

English:
lemma isLE_of_iso
  given: (n : Int) [K.IsLE n]
  statement: L.IsLE n
  proof: by
  apply isSupported_of_iso e

中文:
引理 isLE_of_iso
  条件: (n : 整数) [K.IsLE n]
  结论: L.IsLE n
  证明: by
  apply isSupported_of_iso e

Depends on / 依赖: isSupported_of_iso
-/
lemma isLE_of_iso (n : Int) [K.IsLE n] : L.IsLE n := by
  apply isSupported_of_iso e

/--
lemma `isGE_of_iso` / 引理 `isGE_of_iso`

English:
lemma isGE_of_iso
  given: (n : Int) [K.IsGE n]
  statement: L.IsGE n
  proof: by
  apply isSupported_of_iso e

中文:
引理 isGE_of_iso
  条件: (n : 整数) [K.IsGE n]
  结论: L.IsGE n
  证明: by
  apply isSupported_of_iso e

Depends on / 依赖: isSupported_of_iso
-/
lemma isGE_of_iso (n : Int) [K.IsGE n] : L.IsGE n := by
  apply isSupported_of_iso e

end

section

variable [HasZeroObject C]

instance (X : CochainComplex C Nat) :
    CochainComplex.IsStrictlyGE (X.extend embeddingUpNat) 0 where
  isZero _ _ := isZero_extend_X _ _ _ (by aesop)

instance (X : ChainComplex C Nat) :
    CochainComplex.IsStrictlyLE (X.extend embeddingDownNat) 0 where
  isZero _ _ := isZero_extend_X _ _ _ (by aesop)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `exists_iso_single` / 引理 `exists_iso_single`

English:
lemma exists_iso_single
  given: (n : Int) [K.IsStrictlyGE n] [K.IsStrictlyLE n]
  proof: ⟨K.X n, ⟨{
      hom := mkHomToSingle (𝟙 _) (fun i (hi : i + 1 = n) =>
        (K.isZero_of_isStrictlyGE n i (by lia)).eq_of_src _ _)
      inv := mkHomFromSingle (𝟙 _) (fun i (hi : n + 1 = i) =>
        (K.isZero_of_isStrictlyLE n i (by lia)).eq_of_tgt _ _)
      hom_inv_id := by
        ext i
    

中文:
引理 exists_iso_single
  条件: (n : 整数) [K.IsStrictlyGE n] [K.IsStrictlyLE n]
  证明: ⟨K.X n, ⟨{
      hom := mkHomToSingle (𝟙 _) (fun i (hi : i + 1 = n) =>
        (K.isZero_of_isStrictlyGE n i (by lia)).eq_of_src _ _)
      inv := mkHomFromSingle (𝟙 _) (fun i (hi : n + 1 = i) =>
        (K.isZero_of_isStrictlyLE n i (by lia)).eq_of_tgt _ _)
      hom_inv_id := by
        ext i
    

Depends on / 依赖: K.isZero_of_isStrictlyGE, K.isZero_of_isStrictlyLE, eq_of_src, eq_of_tgt, hom_inv_id, inv_hom_id, isZero_of_isStrictlyGE, isZero_of_isStrictlyLE, lt_trichotomy, mkHomFromSingle, mkHomToSingle
-/
lemma exists_iso_single (n : Int) [K.IsStrictlyGE n] [K.IsStrictlyLE n] :
    exists (M : C), Nonempty (K ≅ (single _ _ n).obj M) :=
  ⟨K.X n, ⟨{
      hom := mkHomToSingle (𝟙 _) (fun i (hi : i + 1 = n) =>
        (K.isZero_of_isStrictlyGE n i (by lia)).eq_of_src _ _)
      inv := mkHomFromSingle (𝟙 _) (fun i (hi : n + 1 = i) =>
        (K.isZero_of_isStrictlyLE n i (by lia)).eq_of_tgt _ _)
      hom_inv_id := by
        ext i
        obtain hi | rfl | hi := lt_trichotomy i n
        · apply (K.isZero_of_isStrictlyGE n i (by lia)).eq_of_src
        · simp
        · apply (K.isZero_of_isStrictlyLE n i (by lia)).eq_of_tgt
      inv_hom_id := by aesop }⟩⟩

instance (A : C) (n : Int) :
    IsStrictlyGE ((single C (ComplexShape.up Int) n).obj A) n := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact isZero_single_obj_X _ _ _ _ (by lia)

instance (A : C) (n : Int) :
    IsStrictlyLE ((single C (ComplexShape.up Int) n).obj A) n := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact isZero_single_obj_X _ _ _ _ (by lia)

variable [forall i, K.HasHomology i] [forall i, L.HasHomology i] (n : Int)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.IsStrictlyGE
  signature: n] : IsIso (K.πTruncGE n)
  body: by dsimp [πTruncGE]; infer_instance

中文:
实例 [K.IsStrictlyGE
  签名: n] : IsIso (K.πTruncGE n)
  定义体: by dsimp [πTruncGE]; infer_instance

Depends on / 依赖: infer_instance
-/
instance [K.IsStrictlyGE n] : IsIso (K.πTruncGE n) := by dsimp [πTruncGE]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.IsStrictlyLE
  signature: n] : IsIso (K.ιTruncLE n)
  body: by dsimp [ιTruncLE]; infer_instance

中文:
实例 [K.IsStrictlyLE
  签名: n] : IsIso (K.ιTruncLE n)
  定义体: by dsimp [ιTruncLE]; infer_instance

Depends on / 依赖: infer_instance
-/
instance [K.IsStrictlyLE n] : IsIso (K.ιTruncLE n) := by dsimp [ιTruncLE]; infer_instance

/--
lemma `isIso_πTruncGE_iff` / 引理 `isIso_πTruncGE_iff`

English:
lemma isIso_πTruncGE_iff
  statement: IsIso (K.πTruncGE n) ↔ K.IsStrictlyGE n
  proof: by
  apply HomologicalComplex.isIso_πTruncGE_iff

中文:
引理 isIso_πTruncGE_iff
  结论: IsIso (K.πTruncGE n) ↔ K.IsStrictlyGE n
  证明: by
  apply HomologicalComplex.isIso_πTruncGE_iff

Depends on / 依赖: HomologicalComplex, HomologicalComplex.isIso_
-/
lemma isIso_πTruncGE_iff : IsIso (K.πTruncGE n) ↔ K.IsStrictlyGE n := by
  apply HomologicalComplex.isIso_πTruncGE_iff

/--
lemma `isIso_ιTruncLE_iff` / 引理 `isIso_ιTruncLE_iff`

English:
lemma isIso_ιTruncLE_iff
  statement: IsIso (K.ιTruncLE n) ↔ K.IsStrictlyLE n
  proof: by
  apply HomologicalComplex.isIso_ιTruncLE_iff

中文:
引理 isIso_ιTruncLE_iff
  结论: IsIso (K.ιTruncLE n) ↔ K.IsStrictlyLE n
  证明: by
  apply HomologicalComplex.isIso_ιTruncLE_iff

Depends on / 依赖: HomologicalComplex, HomologicalComplex.isIso_
-/
lemma isIso_ιTruncLE_iff : IsIso (K.ιTruncLE n) ↔ K.IsStrictlyLE n := by
  apply HomologicalComplex.isIso_ιTruncLE_iff

/--
lemma `quasiIso_πTruncGE_iff` / 引理 `quasiIso_πTruncGE_iff`

English:
lemma quasiIso_πTruncGE_iff
  statement: QuasiIso (K.πTruncGE n) ↔ K.IsGE n
  proof: quasiIso_πTruncGE_iff_isSupported K (embeddingUpIntGE n)

中文:
引理 quasiIso_πTruncGE_iff
  结论: QuasiIso (K.πTruncGE n) ↔ K.IsGE n
  证明: quasiIso_πTruncGE_iff_isSupported K (embeddingUpIntGE n)

Depends on / 依赖: embeddingUpIntGE
-/
lemma quasiIso_πTruncGE_iff : QuasiIso (K.πTruncGE n) ↔ K.IsGE n :=
  quasiIso_πTruncGE_iff_isSupported K (embeddingUpIntGE n)

/--
lemma `quasiIso_ιTruncLE_iff` / 引理 `quasiIso_ιTruncLE_iff`

English:
lemma quasiIso_ιTruncLE_iff
  statement: QuasiIso (K.ιTruncLE n) ↔ K.IsLE n
  proof: quasiIso_ιTruncLE_iff_isSupported K (embeddingUpIntLE n)

中文:
引理 quasiIso_ιTruncLE_iff
  结论: QuasiIso (K.ιTruncLE n) ↔ K.IsLE n
  证明: quasiIso_ιTruncLE_iff_isSupported K (embeddingUpIntLE n)

Depends on / 依赖: embeddingUpIntLE
-/
lemma quasiIso_ιTruncLE_iff : QuasiIso (K.ιTruncLE n) ↔ K.IsLE n :=
  quasiIso_ιTruncLE_iff_isSupported K (embeddingUpIntLE n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.IsGE
  signature: n] : QuasiIso (K.πTruncGE n)
  body: by
  rw [quasiIso_πTruncGE_iff]
  infer_instance

中文:
实例 [K.IsGE
  签名: n] : QuasiIso (K.πTruncGE n)
  定义体: by
  rw [quasiIso_πTruncGE_iff]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance [K.IsGE n] : QuasiIso (K.πTruncGE n) := by
  rw [quasiIso_πTruncGE_iff]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.IsLE
  signature: n] : QuasiIso (K.ιTruncLE n)
  body: by
  rw [quasiIso_ιTruncLE_iff]
  infer_instance

中文:
实例 [K.IsLE
  签名: n] : QuasiIso (K.ιTruncLE n)
  定义体: by
  rw [quasiIso_ιTruncLE_iff]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance [K.IsLE n] : QuasiIso (K.ιTruncLE n) := by
  rw [quasiIso_ιTruncLE_iff]
  infer_instance

variable {K L}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `quasiIso_truncGEMap_iff` / 引理 `quasiIso_truncGEMap_iff`

English:
lemma quasiIso_truncGEMap_iff
  proof: by
  rw [HomologicalComplex.quasiIso_truncGEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.le.dest hi
    exact h k _ rfl
  · rintro h i i' rfl
    exact h _ (by dsimp; lia)

中文:
引理 quasiIso_truncGEMap_iff
  证明: by
  rw [HomologicalComplex.quasiIso_truncGEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.le.dest hi
    exact h k _ rfl
  · rintro h i i' rfl
    exact h _ (by dsimp; lia)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.quasiIso_truncGEMap_iff, Int.le.dest, quasiIso_truncGEMap_iff
-/
lemma quasiIso_truncGEMap_iff :
    QuasiIso (truncGEMap φ n) ↔ forall (i : Int) (_ : n <= i), QuasiIsoAt φ i := by
  rw [HomologicalComplex.quasiIso_truncGEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.le.dest hi
    exact h k _ rfl
  · rintro h i i' rfl
    exact h _ (by dsimp; lia)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `quasiIso_truncLEMap_iff` / 引理 `quasiIso_truncLEMap_iff`

English:
lemma quasiIso_truncLEMap_iff
  proof: by
  rw [HomologicalComplex.quasiIso_truncLEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.le.dest hi
    exact h k _ (by dsimp; lia)
  · rintro h i i' rfl
    exact h _ (by dsimp; lia)

中文:
引理 quasiIso_truncLEMap_iff
  证明: by
  rw [HomologicalComplex.quasiIso_truncLEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.le.dest hi
    exact h k _ (by dsimp; lia)
  · rintro h i i' rfl
    exact h _ (by dsimp; lia)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.quasiIso_truncLEMap_iff, Int.le.dest, quasiIso_truncLEMap_iff
-/
lemma quasiIso_truncLEMap_iff :
    QuasiIso (truncLEMap φ n) ↔ forall (i : Int) (_ : i <= n), QuasiIsoAt φ i := by
  rw [HomologicalComplex.quasiIso_truncLEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.le.dest hi
    exact h k _ (by dsimp; lia)
  · rintro h i i' rfl
    exact h _ (by dsimp; lia)

end

section

variable {D : Type*} [Category* D] [HasZeroMorphisms D]

/--
lemma `isStrictlyGE_mapHomologicalComplex_obj_iff` / 引理 `isStrictlyGE_mapHomologicalComplex_obj_iff`

English:
lemma isStrictlyGE_mapHomologicalComplex_obj_iff
  proof: isStrictlySupported_mapHomologicalComplex_obj_iff ..

中文:
引理 isStrictlyGE_mapHomologicalComplex_obj_iff
  证明: isStrictlySupported_mapHomologicalComplex_obj_iff ..

Depends on / 依赖: infer_instance, isStrictlySupported_mapHomologicalComplex_obj_iff, truncGE
-/
lemma isStrictlyGE_mapHomologicalComplex_obj_iff
    (F : C ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms] (n : Int) :
    CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (.up Int)).obj K) n ↔
      K.IsStrictlyGE n :=
  isStrictlySupported_mapHomologicalComplex_obj_iff ..

/--
lemma `isStrictlyLE_mapHomologicalComplex_obj_iff` / 引理 `isStrictlyLE_mapHomologicalComplex_obj_iff`

English:
lemma isStrictlyLE_mapHomologicalComplex_obj_iff
  proof: isStrictlySupported_mapHomologicalComplex_obj_iff ..

中文:
引理 isStrictlyLE_mapHomologicalComplex_obj_iff
  证明: isStrictlySupported_mapHomologicalComplex_obj_iff ..

Depends on / 依赖: isStrictlySupported_mapHomologicalComplex_obj_iff
-/
lemma isStrictlyLE_mapHomologicalComplex_obj_iff
    (F : C ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms] (n : Int) :
    CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (.up Int)).obj K) n ↔
      K.IsStrictlyLE n :=
  isStrictlySupported_mapHomologicalComplex_obj_iff ..

end

end HasZeroMorphisms

section Preadditive

variable [Preadditive C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] (A
  body: inferInstanceAs (IsStrictlyGE ((single C (ComplexShape.up Int) n).obj A) n)

中文:
实例 [HasZeroObject
  签名: C] (A
  定义体: inferInstanceAs (IsStrictlyGE ((single C (ComplexShape.up Int) n).obj A) n)

Depends on / 依赖: ComplexShape, ComplexShape.up, IsStrictlyGE, single
-/
instance [HasZeroObject C] (A : C) (n : Int) : ((singleFunctor C n).obj A).IsStrictlyGE n :=
  inferInstanceAs (IsStrictlyGE ((single C (ComplexShape.up Int) n).obj A) n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] (A
  body: inferInstanceAs (IsStrictlyLE ((single C (ComplexShape.up Int) n).obj A) n)

中文:
实例 [HasZeroObject
  签名: C] (A
  定义体: inferInstanceAs (IsStrictlyLE ((single C (ComplexShape.up Int) n).obj A) n)

Depends on / 依赖: ComplexShape, ComplexShape.up, IsStrictlyLE, K.quasiIsoAt_, single
-/
instance [HasZeroObject C] (A : C) (n : Int) : ((singleFunctor C n).obj A).IsStrictlyLE n :=
  inferInstanceAs (IsStrictlyLE ((single C (ComplexShape.up Int) n).obj A) n)

variable (K : CochainComplex C Int)

/--
lemma `isStrictlyLE_shift` / 引理 `isStrictlyLE_shift`

English:
lemma isStrictlyLE_shift
  given: (n : Int) [K.IsStrictlyLE n] (a n' : Int) (h : a + n' = n)
  proof: by
  rw [isStrictlyLE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyLE n _ (by lia)) (K.shiftFunctorObjXIso a i _ rfl)

中文:
引理 isStrictlyLE_shift
  条件: (n : 整数) [K.IsStrictlyLE n] (a n' : 整数) (h : a + n' = n)
  证明: by
  rw [isStrictlyLE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyLE n _ (by lia)) (K.shiftFunctorObjXIso a i _ rfl)

Depends on / 依赖: IsZero, IsZero.of_iso, K.isZero_of_isStrictlyLE, K.shiftFunctorObjXIso, isStrictlyLE_iff, isZero_of_isStrictlyLE, of_iso, shiftFunctorObjXIso
-/
lemma isStrictlyLE_shift (n : Int) [K.IsStrictlyLE n] (a n' : Int) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyLE n' := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyLE n _ (by lia)) (K.shiftFunctorObjXIso a i _ rfl)

/--
lemma `isStrictlyGE_shift` / 引理 `isStrictlyGE_shift`

English:
lemma isStrictlyGE_shift
  given: (n : Int) [K.IsStrictlyGE n] (a n' : Int) (h : a + n' = n)
  proof: by
  rw [isStrictlyGE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyGE n _ (by lia)) (K.shiftFunctorObjXIso a i _ rfl)

中文:
引理 isStrictlyGE_shift
  条件: (n : 整数) [K.IsStrictlyGE n] (a n' : 整数) (h : a + n' = n)
  证明: by
  rw [isStrictlyGE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyGE n _ (by lia)) (K.shiftFunctorObjXIso a i _ rfl)

Depends on / 依赖: IsZero, IsZero.of_iso, K.isZero_of_isStrictlyGE, K.shiftFunctorObjXIso, isStrictlyGE_iff, isZero_of_isStrictlyGE, of_iso, shiftFunctorObjXIso
-/
lemma isStrictlyGE_shift (n : Int) [K.IsStrictlyGE n] (a n' : Int) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyGE n' := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyGE n _ (by lia)) (K.shiftFunctorObjXIso a i _ rfl)

section

variable [CategoryWithHomology C]

/--
lemma `isLE_shift` / 引理 `isLE_shift`

English:
lemma isLE_shift
  given: (n : Int) [K.IsLE n] (a n' : Int) (h : a + n' = n)
  statement: (K⟦a⟧).IsLE n'
  proof: by
  rw [isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact IsZero.of_iso (K.isZero_of_isLE n (a + i) (by lia))
    (((homologyFunctor C _ (0 : Int)).shiftIso a i _ rfl).app K)

中文:
引理 isLE_shift
  条件: (n : 整数) [K.IsLE n] (a n' : 整数) (h : a + n' = n)
  结论: (K⟦a⟧).IsLE n'
  证明: by
  rw [isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact IsZero.of_iso (K.isZero_of_isLE n (a + i) (by lia))
    (((homologyFunctor C _ (0 : Int)).shiftIso a i _ rfl).app K)

Depends on / 依赖: IsZero, IsZero.of_iso, K.isZero_of_isLE, exactAt_iff_isZero_homology, homologyFunctor, isLE_iff, isZero_of_isLE, of_iso, shiftIso
-/
lemma isLE_shift (n : Int) [K.IsLE n] (a n' : Int) (h : a + n' = n) : (K⟦a⟧).IsLE n' := by
  rw [isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact IsZero.of_iso (K.isZero_of_isLE n (a + i) (by lia))
    (((homologyFunctor C _ (0 : Int)).shiftIso a i _ rfl).app K)

/--
lemma `isGE_shift` / 引理 `isGE_shift`

English:
lemma isGE_shift
  given: (n : Int) [K.IsGE n] (a n' : Int) (h : a + n' = n)
  statement: (K⟦a⟧).IsGE n'
  proof: by
  rw [isGE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact IsZero.of_iso (K.isZero_of_isGE n (a + i) (by lia))
    (((homologyFunctor C _ (0 : Int)).shiftIso a i _ rfl).app K)

中文:
引理 isGE_shift
  条件: (n : 整数) [K.IsGE n] (a n' : 整数) (h : a + n' = n)
  结论: (K⟦a⟧).IsGE n'
  证明: by
  rw [isGE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact IsZero.of_iso (K.isZero_of_isGE n (a + i) (by lia))
    (((homologyFunctor C _ (0 : Int)).shiftIso a i _ rfl).app K)

Depends on / 依赖: IsZero, IsZero.of_iso, K.isZero_of_isGE, exactAt_iff_isZero_homology, homologyFunctor, isGE_iff, isZero_of_isGE, of_iso, shiftIso
-/
lemma isGE_shift (n : Int) [K.IsGE n] (a n' : Int) (h : a + n' = n) : (K⟦a⟧).IsGE n' := by
  rw [isGE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact IsZero.of_iso (K.isZero_of_isGE n (a + i) (by lia))
    (((homologyFunctor C _ (0 : Int)).shiftIso a i _ rfl).app K)

end

end Preadditive

section HasZeroMorphisms

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
  (K L : CochainComplex C Int) (φ : K ⟶ L) (e : K ≅ L)
  [forall (i : Int), K.HasHomology i] [forall (i : Int), L.HasHomology i] (n : Int)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `truncGEXIso` / `truncGEXIso` 的定义

English:
definition truncGEXIso
  signature: (n i : Int) (hi : n < i := by lia)
  body: HomologicalComplex.truncGEXIso K (embeddingUpIntGE n) (i := (i - n).natAbs) (by
      dsimp
      rw [Int.natAbs_of_nonneg (by lia)]; rw [add_sub_cancel])
    (fun h => by
      rw [boundaryGE_embeddingUpIntGE_iff]; rw [Int.natAbs_eq_zero] at h
      lia)

中文:
定义 truncGEXIso
  签名: (n i : 整数) (hi : n < i := by lia)
  定义体: HomologicalComplex.truncGEXIso K (embeddingUpIntGE n) (i := (i - n).natAbs) (by
      dsimp
      rw [Int.natAbs_of_nonneg (by lia)]; rw [add_sub_cancel])
    (fun h => by
      rw [boundaryGE_embeddingUpIntGE_iff]; rw [Int.natAbs_eq_zero] at h
      lia)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.truncGEXIso, Int.natAbs_eq_zero, Int.natAbs_of_nonneg, K.truncGE, add_sub_cancel, boundaryGE_embeddingUpIntGE_iff, embeddingUpIntGE, natAbs, natAbs_eq_zero, natAbs_of_nonneg, truncGE, truncGEXIso
-/
noncomputable def truncGEXIso (n i : Int) (hi : n < i := by lia) :
    (K.truncGE n).X i ≅ K.X i :=
  HomologicalComplex.truncGEXIso K (embeddingUpIntGE n) (i := (i - n).natAbs) (by
      dsimp
      rw [Int.natAbs_of_nonneg (by lia)]; rw [add_sub_cancel])
    (fun h => by
      rw [boundaryGE_embeddingUpIntGE_iff]; rw [Int.natAbs_eq_zero] at h
      lia)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `truncLEXIso` / `truncLEXIso` 的定义

English:
definition truncLEXIso
  signature: (n i : Int) (hi : i < n := by lia)
  body: HomologicalComplex.truncLEXIso K (embeddingUpIntLE n) (i := (n - i).natAbs) (by
      dsimp
      rw [Int.natAbs_of_nonneg (by lia)]; rw [sub_sub_cancel])
    (fun h => by
      rw [boundaryLE_embeddingUpIntLE_iff]; rw [Int.natAbs_eq_zero] at h
      lia)

中文:
定义 truncLEXIso
  签名: (n i : 整数) (hi : i < n := by lia)
  定义体: HomologicalComplex.truncLEXIso K (embeddingUpIntLE n) (i := (n - i).natAbs) (by
      dsimp
      rw [Int.natAbs_of_nonneg (by lia)]; rw [sub_sub_cancel])
    (fun h => by
      rw [boundaryLE_embeddingUpIntLE_iff]; rw [Int.natAbs_eq_zero] at h
      lia)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.truncLEXIso, Int.natAbs_eq_zero, Int.natAbs_of_nonneg, K.op.truncGE, K.truncLE, boundaryLE_embeddingUpIntLE_iff, e.op, embeddingUpIntLE, natAbs, natAbs_eq_zero, natAbs_of_nonneg, sub_sub_cancel, symm.unop, truncGE, truncLE, truncLEXIso
-/
noncomputable def truncLEXIso (n i : Int) (hi : i < n := by lia) :
    (K.truncLE n).X i ≅ K.X i :=
  HomologicalComplex.truncLEXIso K (embeddingUpIntLE n) (i := (n - i).natAbs) (by
      dsimp
      rw [Int.natAbs_of_nonneg (by lia)]; rw [sub_sub_cancel])
    (fun h => by
      rw [boundaryLE_embeddingUpIntLE_iff]; rw [Int.natAbs_eq_zero] at h
      lia)

/--
Definition of `truncGEXIsoOpcycles` / `truncGEXIsoOpcycles` 的定义

English:
definition truncGEXIsoOpcycles
  signature: (n : Int)
  body: HomologicalComplex.truncGEXIsoOpcycles K (embeddingUpIntGE n) (i := 0) (by simp)
    (by rw [boundaryGE_embeddingUpIntGE_iff])

中文:
定义 truncGEXIsoOpcycles
  签名: (n : 整数)
  定义体: HomologicalComplex.truncGEXIsoOpcycles K (embeddingUpIntGE n) (i := 0) (by simp)
    (by rw [boundaryGE_embeddingUpIntGE_iff])

Depends on / 依赖: HomologicalComplex, HomologicalComplex.truncGEXIsoOpcycles, K.op.truncGE, K.opcyclesOpIso, XIsoOpcycles, boundaryGE_embeddingUpIntGE_iff, e.op, embeddingUpIntGE, opcyclesOpIso, truncGE, truncGEXIsoOpcycles, unop.symm
-/
noncomputable def truncGEXIsoOpcycles (n : Int) :
    (K.truncGE n).X n ≅ K.opcycles n :=
  HomologicalComplex.truncGEXIsoOpcycles K (embeddingUpIntGE n) (i := 0) (by simp)
    (by rw [boundaryGE_embeddingUpIntGE_iff])

/--
Definition of `truncLEXIsoCycles` / `truncLEXIsoCycles` 的定义

English:
definition truncLEXIsoCycles
  signature: (n : Int)
  body: HomologicalComplex.truncLEXIsoCycles K (embeddingUpIntLE n) (i := 0) (by simp)
    (by rw [boundaryLE_embeddingUpIntLE_iff])

中文:
定义 truncLEXIsoCycles
  签名: (n : 整数)
  定义体: HomologicalComplex.truncLEXIsoCycles K (embeddingUpIntLE n) (i := 0) (by simp)
    (by rw [boundaryLE_embeddingUpIntLE_iff])

Depends on / 依赖: HomologicalComplex, HomologicalComplex.truncLEXIsoCycles, K.op.truncGE, Quiver, Quiver.Hom.op_inj, _d_eq, boundaryLE_embeddingUpIntLE_iff, e.op, embeddingUpIntLE, op_inj, truncGE, truncLEXIsoCycles
-/
noncomputable def truncLEXIsoCycles (n : Int) :
    (K.truncLE n).X n ≅ K.cycles n :=
  HomologicalComplex.truncLEXIsoCycles K (embeddingUpIntLE n) (i := 0) (by simp)
    (by rw [boundaryLE_embeddingUpIntLE_iff])

/--
lemma `acyclic_truncGE_iff` / 引理 `acyclic_truncGE_iff`

English:
lemma acyclic_truncGE_iff
  given: (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia)
  proof: by
  dsimp [truncGE]
  rw [acyclic_truncGE_iff_isSupportedOutside]; rw [(Embedding.embeddingUpInt_areComplementary n₀ n₁ h).isSupportedOutside₂_iff]

中文:
引理 acyclic_truncGE_iff
  条件: (n₀ n₁ : 整数) (h : n₀ + 1 = n₁ := by lia)
  证明: by
  dsimp [truncGE]
  rw [acyclic_truncGE_iff_isSupportedOutside]; rw [(Embedding.embeddingUpInt_areComplementary n₀ n₁ h).isSupportedOutside₂_iff]

Depends on / 依赖: Acyclic, Embedding, Embedding.embeddingUpInt_areComplementary, K.IsLE, K.op.truncGE, K.truncGE, Quiver, Quiver.Hom.op_inj, XIsoCycles, _d_eq_fromOpcycles, acyclic_truncGE_iff_isSupportedOutside, e.op, embeddingUpInt_areComplementary, op_inj, truncGE, truncLE
-/
lemma acyclic_truncGE_iff (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia) :
    (K.truncGE n₁).Acyclic ↔ K.IsLE n₀ := by
  dsimp [truncGE]
  rw [acyclic_truncGE_iff_isSupportedOutside]; rw [(Embedding.embeddingUpInt_areComplementary n₀ n₁ h).isSupportedOutside₂_iff]

/--
lemma `acyclic_truncLE_iff` / 引理 `acyclic_truncLE_iff`

English:
lemma acyclic_truncLE_iff
  given: (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia)
  proof: by
  dsimp [truncLE]
  rw [acyclic_truncLE_iff_isSupportedOutside]; rw [(Embedding.embeddingUpInt_areComplementary n₀ n₁ h).isSupportedOutside₁_iff]

中文:
引理 acyclic_truncLE_iff
  条件: (n₀ n₁ : 整数) (h : n₀ + 1 = n₁ := by lia)
  证明: by
  dsimp [truncLE]
  rw [acyclic_truncLE_iff_isSupportedOutside]; rw [(Embedding.embeddingUpInt_areComplementary n₀ n₁ h).isSupportedOutside₁_iff]

Depends on / 依赖: Acyclic, Embedding, Embedding.embeddingUpInt_areComplementary, K.IsGE, K.truncLE, acyclic_truncLE_iff_isSupportedOutside, embeddingUpInt_areComplementary, truncLE
-/
lemma acyclic_truncLE_iff (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia) :
    (K.truncLE n₀).Acyclic ↔ K.IsGE n₁ := by
  dsimp [truncLE]
  rw [acyclic_truncLE_iff_isSupportedOutside]; rw [(Embedding.embeddingUpInt_areComplementary n₀ n₁ h).isSupportedOutside₁_iff]

end HasZeroMorphisms

section Abelian

variable [Abelian C] (K L : CochainComplex C Int)

/--
Definition of `shortComplexTruncLE` / `shortComplexTruncLE` 的定义

English:
abbreviation shortComplexTruncLE
  signature: (n : Int)
  body: HomologicalComplex.shortComplexTruncLE K (embeddingUpIntLE n)

中文:
缩写 shortComplexTruncLE
  签名: (n : 整数)
  定义体: HomologicalComplex.shortComplexTruncLE K (embeddingUpIntLE n)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.shortComplexTruncLE, embeddingUpIntLE, shortComplexTruncLE
-/
noncomputable abbrev shortComplexTruncLE (n : Int) : ShortComplex (CochainComplex C Int) :=
  HomologicalComplex.shortComplexTruncLE K (embeddingUpIntLE n)

/--
lemma `shortComplexTruncLE_shortExact` / 引理 `shortComplexTruncLE_shortExact`

English:
lemma shortComplexTruncLE_shortExact
  given: (n : Int)
  proof: by
  apply HomologicalComplex.shortComplexTruncLE_shortExact

中文:
引理 shortComplexTruncLE_shortExact
  条件: (n : 整数)
  证明: by
  apply HomologicalComplex.shortComplexTruncLE_shortExact

Depends on / 依赖: HomologicalComplex, HomologicalComplex.shortComplexTruncLE_shortExact, shortComplexTruncLE_shortExact
-/
lemma shortComplexTruncLE_shortExact (n : Int) :
    (K.shortComplexTruncLE n).ShortExact := by
  apply HomologicalComplex.shortComplexTruncLE_shortExact

variable (n₀ n₁ : Int)

/--
Definition of `shortComplexTruncLEX₃ToTruncGE` / `shortComplexTruncLEX₃ToTruncGE` 的定义

English:
abbreviation shortComplexTruncLEX₃ToTruncGE
  signature: (h : n₀ + 1 = n₁ := by lia)
  body: HomologicalComplex.shortComplexTruncLEX₃ToTruncGE K
    (Embedding.embeddingUpInt_areComplementary n₀ n₁ h)

@[reassoc]

中文:
缩写 shortComplexTruncLEX₃ToTruncGE
  签名: (h : n₀ + 1 = n₁ := by lia)
  定义体: HomologicalComplex.shortComplexTruncLEX₃ToTruncGE K
    (Embedding.embeddingUpInt_areComplementary n₀ n₁ h)

@[reassoc]

Depends on / 依赖: Embedding, Embedding.embeddingUpInt_areComplementary, HomologicalComplex, HomologicalComplex.shortComplexTruncLEX, K.shortComplexTruncLE, K.truncGE, embeddingUpInt_areComplementary, shortComplexTruncLE, truncGE
-/
noncomputable abbrev shortComplexTruncLEX₃ToTruncGE (h : n₀ + 1 = n₁ := by lia) :
    (K.shortComplexTruncLE n₀).X₃ ⟶ K.truncGE n₁ :=
  HomologicalComplex.shortComplexTruncLEX₃ToTruncGE K
    (Embedding.embeddingUpInt_areComplementary n₀ n₁ h)

@[reassoc]
/--
lemma `g_shortComplexTruncLEX₃ToTruncGE` / 引理 `g_shortComplexTruncLEX₃ToTruncGE`

English:
lemma g_shortComplexTruncLEX₃ToTruncGE
  given: (h : n₀ + 1 = n₁ := by lia)
  proof: by
  apply HomologicalComplex.g_shortComplexTruncLEX₃ToTruncGE

中文:
引理 g_shortComplexTruncLEX₃ToTruncGE
  条件: (h : n₀ + 1 = n₁ := by lia)
  证明: by
  apply HomologicalComplex.g_shortComplexTruncLEX₃ToTruncGE

Depends on / 依赖: HomologicalComplex, HomologicalComplex.g_shortComplexTruncLEX, K.shortComplexTruncLE, K.shortComplexTruncLEX, c.symm, e.op, opFunctor, shortComplexTruncLE, truncGE, unopFunctor
-/
lemma g_shortComplexTruncLEX₃ToTruncGE (h : n₀ + 1 = n₁ := by lia) :
    (K.shortComplexTruncLE n₀).g ≫ K.shortComplexTruncLEX₃ToTruncGE n₀ n₁ h = K.πTruncGE n₁ := by
  apply HomologicalComplex.g_shortComplexTruncLEX₃ToTruncGE

/--
lemma `injective_opcycles` / 引理 `injective_opcycles`

English:
lemma injective_opcycles
  statement: [Injective (K.X n₀)] [Injective (K.X n₁)]
  proof: by
  let S : ShortComplex C := ShortComplex.mk (K.d n₀ n₁) (K.pOpcycles n₁) (by simp)
  have : Mono S.f := by
    let T := K.sc' (n₀ - 1) n₀ n₁
    have hT : T.Exact := by
      rwa [← K.exactAt_iff' (n₀ - 1) n₀ n₁ (by simp) (by simpa)]
    exact hT.mono_g ((K.isZero_of_isStrictlyGE n₀ _).eq_of_src 

中文:
引理 injective_opcycles
  结论: [Injective (K.X n₀)] [Injective (K.X n₁)]
  证明: by
  let S : ShortComplex C := ShortComplex.mk (K.d n₀ n₁) (K.pOpcycles n₁) (by simp)
  have : Mono S.f := by
    let T := K.sc' (n₀ - 1) n₀ n₁
    have hT : T.Exact := by
      rwa [← K.exactAt_iff' (n₀ - 1) n₀ n₁ (by simp) (by simpa)]
    exact hT.mono_g ((K.isZero_of_isStrictlyGE n₀ _).eq_of_src 

Depends on / 依赖: Injective, Iso.hom_inv_id_assoc, K.exactAt_iff, K.isZero_of_isStrictlyGE, K.opcycles, K.opcyclesIsCokernel, K.pOpcycles, K.sc, Map_f_eq_opcyclesMap, Quiver, Quiver.Hom.op_inj, Retract, Retract.injective, S.ShortExact, S.exact_of_g_is_cokernel, ShortComplex, ShortComplex.mk, ShortExact, T.Exact, XIsoCycles
-/
lemma injective_opcycles [Injective (K.X n₀)] [Injective (K.X n₁)]
    [K.IsStrictlyGE n₀] (hK : K.ExactAt n₀) (h : n₀ + 1 = n₁ := by lia) :
    Injective (K.opcycles n₁) := by
  let S : ShortComplex C := ShortComplex.mk (K.d n₀ n₁) (K.pOpcycles n₁) (by simp)
  have : Mono S.f := by
    let T := K.sc' (n₀ - 1) n₀ n₁
    have hT : T.Exact := by
      rwa [← K.exactAt_iff' (n₀ - 1) n₀ n₁ (by simp) (by simpa)]
    exact hT.mono_g ((K.isZero_of_isStrictlyGE n₀ _).eq_of_src ..)
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel (K.opcyclesIsCokernel n₀ n₁ (by simp [← h])) }
  exact Retract.injective
    { i := _, r := _, retract := (hS.splittingOfInjective).s_g }

end Abelian

end CochainComplex
