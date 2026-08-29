/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Tower
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Results on finite dimensionality and algebraicity of intermediate fields.
-/

@[expose] public section

open Module

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {S : IntermediateField K L}

/--
theorem `IntermediateField.coe_isIntegral_iff` / 定理 `IntermediateField.coe_isIntegral_iff`

English:
theorem IntermediateField.coe_isIntegral_iff
  statement: {R : Type*} [CommRing R] [Algebra R K] [Algebra R L]
  proof: isIntegral_algHom_iff (S.val.restrictScalars R) Subtype.val_injective

中文:
定理 IntermediateField.coe_isIntegral_iff
  结论: {R : 类型} [CommRing R] [Algebra R K] [Algebra R L]
  证明: isIntegral_algHom_iff (S.val.restrictScalars R) Subtype.val_injective

Depends on / 依赖: S.val.restrictScalars, Subtype, Subtype.val_injective, isIntegral_algHom_iff, restrictScalars, val_injective
-/
theorem IntermediateField.coe_isIntegral_iff {R : Type*} [CommRing R] [Algebra R K] [Algebra R L]
    [IsScalarTower R K L] {x : S} : IsIntegral R (x : L) ↔ IsIntegral R x :=
  isIntegral_algHom_iff (S.val.restrictScalars R) Subtype.val_injective

/--
Definition of `Subalgebra.IsAlgebraic.toIntermediateField` / `Subalgebra.IsAlgebraic.toIntermediateField` 的定义

English:
definition Subalgebra.IsAlgebraic.toIntermediateField
  signature: {S : Subalgebra K L} (hS : S.IsAlgebraic)
  body: S
  inv_mem' x hx := Algebra.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr hx) (hS x hx).isIntegral.inv_mem_adjoin

中文:
定义 Subalgebra.IsAlgebraic.toIntermediateField
  签名: {S : Subalgebra K L} (hS : S.IsAlgebraic)
  定义体: S
  inv_mem' x hx := Algebra.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr hx) (hS x hx).isIntegral.inv_mem_adjoin
-/
def Subalgebra.IsAlgebraic.toIntermediateField {S : Subalgebra K L} (hS : S.IsAlgebraic) :
    IntermediateField K L where
  toSubalgebra := S
  inv_mem' x hx := Algebra.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr hx) (hS x hx).isIntegral.inv_mem_adjoin

/--
Definition of `Algebra.IsAlgebraic.toIntermediateField` / `Algebra.IsAlgebraic.toIntermediateField` 的定义

English:
abbreviation Algebra.IsAlgebraic.toIntermediateField
  signature: (S : Subalgebra K L) [Algebra.IsAlgebraic K S]
  body: (S.isAlgebraic_iff.mpr ‹_›).toIntermediateField

中文:
缩写 Algebra.IsAlgebraic.toIntermediateField
  签名: (S : Subalgebra K L) [Algebra.IsAlgebraic K S]
  定义体: (S.isAlgebraic_iff.mpr ‹_›).toIntermediateField

Depends on / 依赖: S.isAlgebraic_iff.mpr, isAlgebraic_iff, toIntermediateField
-/
abbrev Algebra.IsAlgebraic.toIntermediateField (S : Subalgebra K L) [Algebra.IsAlgebraic K S] :
    IntermediateField K L := (S.isAlgebraic_iff.mpr ‹_›).toIntermediateField

namespace IntermediateField

/--
Instance `isAlgebraic_tower_bot` / 实例 `isAlgebraic_tower_bot`

English:
instance isAlgebraic_tower_bot
  signature: [Algebra.IsAlgebraic K L]
  body: Algebra.IsAlgebraic.of_injective S.val S.val.injective

中文:
实例 isAlgebraic_tower_bot
  签名: [Algebra.IsAlgebraic K L]
  定义体: Algebra.IsAlgebraic.of_injective S.val S.val.injective

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.of_injective, IsAlgebraic, S.val, S.val.injective, injective, of_injective
-/
instance isAlgebraic_tower_bot [Algebra.IsAlgebraic K L] : Algebra.IsAlgebraic K S :=
  Algebra.IsAlgebraic.of_injective S.val S.val.injective

/--
Instance `isAlgebraic_tower_top` / 实例 `isAlgebraic_tower_top`

English:
instance isAlgebraic_tower_top
  signature: [Algebra.IsAlgebraic K L]
  body: Algebra.IsAlgebraic.tower_top (K := K) S

中文:
实例 isAlgebraic_tower_top
  签名: [Algebra.IsAlgebraic K L]
  定义体: Algebra.IsAlgebraic.tower_top (K := K) S

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.tower_top, IsAlgebraic, tower_top
-/
instance isAlgebraic_tower_top [Algebra.IsAlgebraic K L] : Algebra.IsAlgebraic S L :=
  Algebra.IsAlgebraic.tower_top (K := K) S

section FiniteDimensional

variable (F E : IntermediateField K L)

/--
Instance `finiteDimensional_left` / 实例 `finiteDimensional_left`

English:
instance finiteDimensional_left
  signature: [FiniteDimensional K L]
  body: .left K F L

中文:
实例 finiteDimensional_left
  签名: [FiniteDimensional K L]
  定义体: .left K F L
-/
instance finiteDimensional_left [FiniteDimensional K L] : FiniteDimensional K F := .left K F L
/--
Instance `finiteDimensional_right` / 实例 `finiteDimensional_right`

English:
instance finiteDimensional_right
  signature: [FiniteDimensional K L]
  body: .right K F L

@[simp]

中文:
实例 finiteDimensional_right
  签名: [FiniteDimensional K L]
  定义体: .right K F L

@[simp]
-/
instance finiteDimensional_right [FiniteDimensional K L] : FiniteDimensional F L := .right K F L

@[simp]
/--
theorem `rank_eq_rank_subalgebra` / 定理 `rank_eq_rank_subalgebra`

English:
theorem rank_eq_rank_subalgebra
  statement: Module.rank K F.toSubalgebra = Module.rank K F
  proof: rfl

@[simp]

中文:
定理 rank_eq_rank_subalgebra
  结论: Module.rank K F.toSubalgebra = Module.rank K F
  证明: rfl

@[simp]
-/
theorem rank_eq_rank_subalgebra : Module.rank K F.toSubalgebra = Module.rank K F :=
  rfl

@[simp]
/--
theorem `finrank_eq_finrank_subalgebra` / 定理 `finrank_eq_finrank_subalgebra`

English:
theorem finrank_eq_finrank_subalgebra
  statement: finrank K F.toSubalgebra = finrank K F
  proof: rfl

中文:
定理 finrank_eq_finrank_subalgebra
  结论: finrank K F.toSubalgebra = finrank K F
  证明: rfl
-/
theorem finrank_eq_finrank_subalgebra : finrank K F.toSubalgebra = finrank K F :=
  rfl

variable {F} {E}

/--
theorem `eq_of_le_of_finrank_le` / 定理 `eq_of_le_of_finrank_le`

English:
theorem eq_of_le_of_finrank_le
  statement: [hfin : FiniteDimensional K E] (h_le : F <= E)
  proof: haveI : Module.Finite K E.toSubalgebra := hfin
toSubalgebra_injective Subalgebra.eq_of_le_of_finrank_le h_le h_finrank

中文:
定理 eq_of_le_of_finrank_le
  结论: [hfin : FiniteDimensional K E] (h_le : F <= E)
  证明: haveI : Module.Finite K E.toSubalgebra := hfin
toSubalgebra_injective Subalgebra.eq_of_le_of_finrank_le h_le h_finrank

Depends on / 依赖: E.toSubalgebra, Finite, Module, Module.Finite, Subalgebra, Subalgebra.eq_of_le_of_finrank_le, eq_of_le_of_finrank_le, h_finrank, h_le, toSubalgebra, toSubalgebra_injective
-/
theorem eq_of_le_of_finrank_le [hfin : FiniteDimensional K E] (h_le : F <= E)
    (h_finrank : finrank K E <= finrank K F) : F = E :=
  haveI : Module.Finite K E.toSubalgebra := hfin
toSubalgebra_injective Subalgebra.eq_of_le_of_finrank_le h_le h_finrank

/--
theorem `eq_of_le_of_finrank_eq` / 定理 `eq_of_le_of_finrank_eq`

English:
theorem eq_of_le_of_finrank_eq
  statement: [FiniteDimensional K E] (h_le : F <= E)
  proof: eq_of_le_of_finrank_le h_le h_finrank.ge

中文:
定理 eq_of_le_of_finrank_eq
  结论: [FiniteDimensional K E] (h_le : F <= E)
  证明: eq_of_le_of_finrank_le h_le h_finrank.ge

Depends on / 依赖: eq_of_le_of_finrank_le, h_finrank, h_finrank.ge, h_le
-/
theorem eq_of_le_of_finrank_eq [FiniteDimensional K E] (h_le : F <= E)
    (h_finrank : finrank K F = finrank K E) : F = E :=
  eq_of_le_of_finrank_le h_le h_finrank.ge

/--
theorem `eq_iff_finrank_eq_of_le` / 定理 `eq_iff_finrank_eq_of_le`

English:
theorem eq_iff_finrank_eq_of_le
  given: [FiniteDimensional K E] (h_le : F <= E)
  proof: ⟨fun h => by rw [h], eq_of_le_of_finrank_eq h_le⟩

中文:
定理 eq_iff_finrank_eq_of_le
  条件: [FiniteDimensional K E] (h_le : F <= E)
  证明: ⟨fun h => by rw [h], eq_of_le_of_finrank_eq h_le⟩

Depends on / 依赖: eq_of_le_of_finrank_eq, h_le
-/
theorem eq_iff_finrank_eq_of_le [FiniteDimensional K E] (h_le : F <= E) :
    F = E ↔ finrank K F = finrank K E :=
  ⟨fun h => by rw [h], eq_of_le_of_finrank_eq h_le⟩

-- If `F ≤ E` are two intermediate fields of a finite extension `L / K` such that
-- `[L : F] ≤ [L : E]`, then `F = E`. Marked as private since it's a direct corollary of
-- `eq_of_le_of_finrank_le'` (the `FiniteDimensional K L` implies `FiniteDimensional F L`
-- automatically by typeclass resolution).
/--
theorem `eq_of_le_of_finrank_le''` / 定理 `eq_of_le_of_finrank_le''`

English:
theorem eq_of_le_of_finrank_le''
  statement: [FiniteDimensional K L] (h_le : F <= E)
  proof: by
  apply eq_of_le_of_finrank_le h_le
  have h1 := finrank_mul_finrank K F L
  have h2 := finrank_mul_finrank K E L
  have h3 : 0 < finrank E L := finrank_pos
  nlinarith

中文:
定理 eq_of_le_of_finrank_le''
  结论: [FiniteDimensional K L] (h_le : F <= E)
  证明: by
  apply eq_of_le_of_finrank_le h_le
  have h1 := finrank_mul_finrank K F L
  have h2 := finrank_mul_finrank K E L
  have h3 : 0 < finrank E L := finrank_pos
  nlinarith
-/
private theorem eq_of_le_of_finrank_le'' [FiniteDimensional K L] (h_le : F <= E)
    (h_finrank : finrank F L <= finrank E L) : F = E := by
  apply eq_of_le_of_finrank_le h_le
  have h1 := finrank_mul_finrank K F L
  have h2 := finrank_mul_finrank K E L
  have h3 : 0 < finrank E L := finrank_pos
  nlinarith

/--
theorem `eq_of_le_of_finrank_le'` / 定理 `eq_of_le_of_finrank_le'`

English:
theorem eq_of_le_of_finrank_le'
  statement: [FiniteDimensional F L] (h_le : F <= E)
  proof: by
  refine le_antisymm h_le (fun l hl => ?_)
  rwa [← mem_extendScalars (le_refl F), eq_of_le_of_finrank_le''
    ((extendScalars_le_extendScalars_iff (le_refl F) h_le).2 h_le) h_finrank, mem_extendScalars]

中文:
定理 eq_of_le_of_finrank_le'
  结论: [FiniteDimensional F L] (h_le : F <= E)
  证明: by
  refine le_antisymm h_le (fun l hl => ?_)
  rwa [← mem_extendScalars (le_refl F), eq_of_le_of_finrank_le''
    ((extendScalars_le_extendScalars_iff (le_refl F) h_le).2 h_le) h_finrank, mem_extendScalars]

Depends on / 依赖: eq_of_le_of_finrank_le, extendScalars_le_extendScalars_iff, h_finrank, h_le, le_antisymm, le_refl, mem_extendScalars
-/
theorem eq_of_le_of_finrank_le' [FiniteDimensional F L] (h_le : F <= E)
    (h_finrank : finrank F L <= finrank E L) : F = E := by
  refine le_antisymm h_le (fun l hl => ?_)
  rwa [← mem_extendScalars (le_refl F), eq_of_le_of_finrank_le''
    ((extendScalars_le_extendScalars_iff (le_refl F) h_le).2 h_le) h_finrank, mem_extendScalars]

/--
theorem `eq_of_le_of_finrank_eq'` / 定理 `eq_of_le_of_finrank_eq'`

English:
theorem eq_of_le_of_finrank_eq'
  statement: [FiniteDimensional F L] (h_le : F <= E)
  proof: eq_of_le_of_finrank_le' h_le h_finrank.le

中文:
定理 eq_of_le_of_finrank_eq'
  结论: [FiniteDimensional F L] (h_le : F <= E)
  证明: eq_of_le_of_finrank_le' h_le h_finrank.le

Depends on / 依赖: eq_of_le_of_finrank_le, h_finrank, h_finrank.le, h_le
-/
theorem eq_of_le_of_finrank_eq' [FiniteDimensional F L] (h_le : F <= E)
    (h_finrank : finrank F L = finrank E L) : F = E :=
  eq_of_le_of_finrank_le' h_le h_finrank.le

/--
theorem `eq_iff_finrank_eq_of_le'` / 定理 `eq_iff_finrank_eq_of_le'`

English:
theorem eq_iff_finrank_eq_of_le'
  given: [FiniteDimensional F L] (h_le : F <= E)
  proof: ⟨fun h => by rw [h], eq_of_le_of_finrank_eq' h_le⟩

中文:
定理 eq_iff_finrank_eq_of_le'
  条件: [FiniteDimensional F L] (h_le : F <= E)
  证明: ⟨fun h => by rw [h], eq_of_le_of_finrank_eq' h_le⟩

Depends on / 依赖: eq_of_le_of_finrank_eq, h_le
-/
theorem eq_iff_finrank_eq_of_le' [FiniteDimensional F L] (h_le : F <= E) :
    F = E ↔ finrank F L = finrank E L :=
  ⟨fun h => by rw [h], eq_of_le_of_finrank_eq' h_le⟩

/--
lemma `finrank_lt_of_gt` / 引理 `finrank_lt_of_gt`

English:
lemma finrank_lt_of_gt
  given: [FiniteDimensional F L] (H : F < E)
  proof: by
  let := (IntermediateField.inclusion H.le).toAlgebra
  have : IsScalarTower F E L := .of_algebraMap_eq' rfl
  refine lt_of_le_of_ne ?_ ?_
  · exact Module.finrank_top_le_finrank_of_isScalarTower _ _ _
  · exact .symm (mt (eq_of_le_of_finrank_eq' H.le) H.ne)

中文:
引理 finrank_lt_of_gt
  条件: [FiniteDimensional F L] (H : F < E)
  证明: by
  let := (IntermediateField.inclusion H.le).toAlgebra
  have : IsScalarTower F E L := .of_algebraMap_eq' rfl
  refine lt_of_le_of_ne ?_ ?_
  · exact Module.finrank_top_le_finrank_of_isScalarTower _ _ _
  · exact .symm (mt (eq_of_le_of_finrank_eq' H.le) H.ne)

Depends on / 依赖: H.le, H.ne, IntermediateField, IntermediateField.inclusion, IsScalarTower, Module, Module.finrank_top_le_finrank_of_isScalarTower, eq_of_le_of_finrank_eq, finrank_top_le_finrank_of_isScalarTower, inclusion, lt_of_le_of_ne, of_algebraMap_eq, toAlgebra
-/
lemma finrank_lt_of_gt [FiniteDimensional F L] (H : F < E) :
    Module.finrank E L < Module.finrank F L := by
  let := (IntermediateField.inclusion H.le).toAlgebra
  have : IsScalarTower F E L := .of_algebraMap_eq' rfl
  refine lt_of_le_of_ne ?_ ?_
  · exact Module.finrank_top_le_finrank_of_isScalarTower _ _ _
  · exact .symm (mt (eq_of_le_of_finrank_eq' H.le) H.ne)

/--
theorem `finrank_dvd_of_le_left` / 定理 `finrank_dvd_of_le_left`

English:
theorem finrank_dvd_of_le_left
  given: (h : F <= E)
  statement: finrank E L ∣ finrank F L
  proof: by
  let _ := (inclusion h).toRingHom.toAlgebra
  have : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq fun x => rfl
  exact Module.finrank_dvd_finrank_left F E L

中文:
定理 finrank_dvd_of_le_left
  条件: (h : F <= E)
  结论: finrank E L ∣ finrank F L
  证明: by
  let _ := (inclusion h).toRingHom.toAlgebra
  have : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq fun x => rfl
  exact Module.finrank_dvd_finrank_left F E L

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, Module, Module.finrank_dvd_finrank_left, finrank_dvd_finrank_left, inclusion, of_algebraMap_eq, toAlgebra, toRingHom, toRingHom.toAlgebra
-/
theorem finrank_dvd_of_le_left (h : F <= E) : finrank E L ∣ finrank F L := by
  let _ := (inclusion h).toRingHom.toAlgebra
  have : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq fun x => rfl
  exact Module.finrank_dvd_finrank_left F E L

/--
theorem `finrank_dvd_of_le_right` / 定理 `finrank_dvd_of_le_right`

English:
theorem finrank_dvd_of_le_right
  given: (h : F <= E)
  statement: finrank K F ∣ finrank K E
  proof: by
  let _ := (inclusion h).toRingHom.toAlgebra
  exact Module.finrank_dvd_finrank_right K F E

中文:
定理 finrank_dvd_of_le_right
  条件: (h : F <= E)
  结论: finrank K F ∣ finrank K E
  证明: by
  let _ := (inclusion h).toRingHom.toAlgebra
  exact Module.finrank_dvd_finrank_right K F E

Depends on / 依赖: Module, Module.finrank_dvd_finrank_right, finrank_dvd_finrank_right, inclusion, toAlgebra, toRingHom, toRingHom.toAlgebra
-/
theorem finrank_dvd_of_le_right (h : F <= E) : finrank K F ∣ finrank K E := by
  let _ := (inclusion h).toRingHom.toAlgebra
  exact Module.finrank_dvd_finrank_right K F E

/--
theorem `finrank_le_of_le_left` / 定理 `finrank_le_of_le_left`

English:
theorem finrank_le_of_le_left
  given: [FiniteDimensional F L] (h : F <= E)
  statement: finrank E L <= finrank F L
  proof: Nat.le_of_dvd Module.finrank_pos (finrank_dvd_of_le_left h)

中文:
定理 finrank_le_of_le_left
  条件: [FiniteDimensional F L] (h : F <= E)
  结论: finrank E L <= finrank F L
  证明: Nat.le_of_dvd Module.finrank_pos (finrank_dvd_of_le_left h)

Depends on / 依赖: Module, Module.finrank_pos, Nat.le_of_dvd, finrank_dvd_of_le_left, finrank_pos, le_of_dvd
-/
theorem finrank_le_of_le_left [FiniteDimensional F L] (h : F <= E) : finrank E L <= finrank F L :=
  Nat.le_of_dvd Module.finrank_pos (finrank_dvd_of_le_left h)

/--
theorem `finrank_le_of_le_right` / 定理 `finrank_le_of_le_right`

English:
theorem finrank_le_of_le_right
  given: [FiniteDimensional K E] (h : F <= E)
  statement: finrank K F <= finrank K E
  proof: Nat.le_of_dvd Module.finrank_pos (finrank_dvd_of_le_right h)

中文:
定理 finrank_le_of_le_right
  条件: [FiniteDimensional K E] (h : F <= E)
  结论: finrank K F <= finrank K E
  证明: Nat.le_of_dvd Module.finrank_pos (finrank_dvd_of_le_right h)

Depends on / 依赖: Module, Module.finrank_pos, Nat.le_of_dvd, finrank_dvd_of_le_right, finrank_pos, le_of_dvd
-/
theorem finrank_le_of_le_right [FiniteDimensional K E] (h : F <= E) : finrank K F <= finrank K E :=
  Nat.le_of_dvd Module.finrank_pos (finrank_dvd_of_le_right h)

/--
Instance `finiteDimensional_map` / 实例 `finiteDimensional_map`

English:
instance finiteDimensional_map
  signature: (f : L ->ₐ[K] L) [FiniteDimensional K E]
  body: LinearEquiv.finiteDimensional (IntermediateField.equivMap E f).toLinearEquiv

中文:
实例 finiteDimensional_map
  签名: (f : L ->ₐ[K] L) [FiniteDimensional K E]
  定义体: LinearEquiv.finiteDimensional (IntermediateField.equivMap E f).toLinearEquiv

Depends on / 依赖: IntermediateField, IntermediateField.equivMap, LinearEquiv, LinearEquiv.finiteDimensional, equivMap, finiteDimensional, toLinearEquiv
-/
instance finiteDimensional_map (f : L ->ₐ[K] L) [FiniteDimensional K E] :
    FiniteDimensional K (E.map f) :=
  LinearEquiv.finiteDimensional (IntermediateField.equivMap E f).toLinearEquiv

end FiniteDimensional

/--
theorem `isAlgebraic_iff` / 定理 `isAlgebraic_iff`

English:
theorem isAlgebraic_iff
  given: {x : S}
  statement: IsAlgebraic K x ↔ IsAlgebraic K (x : L)
  proof: (isAlgebraic_algebraMap_iff (algebraMap S L).injective).symm

中文:
定理 isAlgebraic_iff
  条件: {x : S}
  结论: IsAlgebraic K x ↔ IsAlgebraic K (x : L)
  证明: (isAlgebraic_algebraMap_iff (algebraMap S L).injective).symm

Depends on / 依赖: algebraMap, injective, isAlgebraic_algebraMap_iff
-/
theorem isAlgebraic_iff {x : S} : IsAlgebraic K x ↔ IsAlgebraic K (x : L) :=
  (isAlgebraic_algebraMap_iff (algebraMap S L).injective).symm

/--
theorem `isIntegral_iff` / 定理 `isIntegral_iff`

English:
theorem isIntegral_iff
  given: {x : S}
  statement: IsIntegral K x ↔ IsIntegral K (x : L)
  proof: (isIntegral_algHom_iff S.val S.val.injective).symm

中文:
定理 isIntegral_iff
  条件: {x : S}
  结论: Is整数egral K x ↔ Is整数egral K (x : L)
  证明: (isIntegral_algHom_iff S.val S.val.injective).symm

Depends on / 依赖: S.val, S.val.injective, injective, isIntegral_algHom_iff
-/
theorem isIntegral_iff {x : S} : IsIntegral K x ↔ IsIntegral K (x : L) :=
  (isIntegral_algHom_iff S.val S.val.injective).symm

/--
theorem `minpoly_eq` / 定理 `minpoly_eq`

English:
theorem minpoly_eq
  given: (x : S)
  statement: minpoly K x = minpoly K (x : L)
  proof: (minpoly.algebraMap_eq (algebraMap S L).injective x).symm

中文:
定理 minpoly_eq
  条件: (x : S)
  结论: minpoly K x = minpoly K (x : L)
  证明: (minpoly.algebraMap_eq (algebraMap S L).injective x).symm

Depends on / 依赖: algebraMap, algebraMap_eq, injective, minpoly, minpoly.algebraMap_eq
-/
theorem minpoly_eq (x : S) : minpoly K x = minpoly K (x : L) :=
  (minpoly.algebraMap_eq (algebraMap S L).injective x).symm

end IntermediateField

/--
Definition of `subalgebraEquivIntermediateField` / `subalgebraEquivIntermediateField` 的定义

English:
definition subalgebraEquivIntermediateField
  signature: [Algebra.IsAlgebraic K L]
  body: S.toIntermediateField fun x hx => S.inv_mem_of_algebraic
    (Algebra.IsAlgebraic.isAlgebraic ((⟨x, hx⟩ : S) : L))
  invFun S := S.toSubalgebra
  left_inv _ := toSubalgebra_toIntermediateField _ _
  right_inv := toIntermediateField_toSubalgebra
  map_rel_iff' := Iff.rfl

@[simp]

中文:
定义 subalgebraEquivIntermediateField
  签名: [Algebra.IsAlgebraic K L]
  定义体: S.toIntermediateField fun x hx => S.inv_mem_of_algebraic
    (Algebra.IsAlgebraic.isAlgebraic ((⟨x, hx⟩ : S) : L))
  invFun S := S.toSubalgebra
  left_inv _ := toSubalgebra_toIntermediateField _ _
  right_inv := toIntermediateField_toSubalgebra
  map_rel_iff' := Iff.rfl

@[simp]

Depends on / 依赖: S.inv_mem_of_algebraic, S.toIntermediateField, inv_mem_of_algebraic, toIntermediateField
-/
def subalgebraEquivIntermediateField [Algebra.IsAlgebraic K L] :
    Subalgebra K L ≃o IntermediateField K L where
  toFun S := S.toIntermediateField fun x hx => S.inv_mem_of_algebraic
    (Algebra.IsAlgebraic.isAlgebraic ((⟨x, hx⟩ : S) : L))
  invFun S := S.toSubalgebra
  left_inv _ := toSubalgebra_toIntermediateField _ _
  right_inv := toIntermediateField_toSubalgebra
  map_rel_iff' := Iff.rfl

@[simp]
/--
theorem `mem_subalgebraEquivIntermediateField` / 定理 `mem_subalgebraEquivIntermediateField`

English:
theorem mem_subalgebraEquivIntermediateField
  statement: [Algebra.IsAlgebraic K L] {S : Subalgebra K L}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_subalgebraEquivIntermediateField
  结论: [Algebra.IsAlgebraic K L] {S : Subalgebra K L}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_subalgebraEquivIntermediateField [Algebra.IsAlgebraic K L] {S : Subalgebra K L}
    {x : L} : x in subalgebraEquivIntermediateField S ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `mem_subalgebraEquivIntermediateField_symm` / 定理 `mem_subalgebraEquivIntermediateField_symm`

English:
theorem mem_subalgebraEquivIntermediateField_symm
  statement: [Algebra.IsAlgebraic K L]
  proof: Iff.rfl

中文:
定理 mem_subalgebraEquivIntermediateField_symm
  结论: [Algebra.IsAlgebraic K L]
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_subalgebraEquivIntermediateField_symm [Algebra.IsAlgebraic K L]
    {S : IntermediateField K L} {x : L} :
    x in subalgebraEquivIntermediateField.symm S ↔ x in S :=
  Iff.rfl
