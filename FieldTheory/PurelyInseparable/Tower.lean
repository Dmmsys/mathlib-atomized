/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!

# Tower law for purely inseparable extensions

This file contains results related to `Field.sepDegree`, `Field.insepDegree` and the tower law.

## Main results

- `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`: the separable degrees satisfy the
  tower law: $[E:F]_s [K:E]_s = [K:F]_s$.

- `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`:
  `Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic`: the inseparable degrees satisfy the
  tower law: $[E:F]_i [K:E]_i = [K:F]_i$.

- `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable`,
  `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'`:
  if `K / E / F` is a field extension tower, such that `E / F` is purely inseparable, then
  for any subset `S` of `K` such that `F(S) / F` is algebraic, the `E(S) / E` and `F(S) / F` have
  the same separable degree. In particular, if `S` is an intermediate field of `K / F` such that
  `S / F` is algebraic, the `E(S) / E` and `S / F` have the same separable degree.

- `minpoly.map_eq_of_isSeparable_of_isPurelyInseparable`: if `K / E / F` is a field extension tower,
  such that `E / F` is purely inseparable, then for any element `x` of `K` separable over `F`,
  it has the same minimal polynomials over `F` and over `E`.

- `Polynomial.Separable.map_irreducible_of_isPurelyInseparable`: if `E / F` is purely inseparable,
  `f` is a separable irreducible polynomial over `F`, then it is also irreducible over `E`.

## Tags

separable degree, degree, separable closure, purely inseparable

-/

public section

open Polynomial IntermediateField Field

noncomputable section

universe u v w

section TowerLaw

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

variable [Algebra E K] [IsScalarTower F E K]

variable {F K} in
/--
theorem `LinearIndependent.map_of_isPurelyInseparable_of_isSeparable` / 定理 `LinearIndependent.map_of_isPurelyInseparable_of_isSeparable`

English:
theorem LinearIndependent.map_of_isPurelyInseparable_of_isSeparable
  statement: [IsPurelyInseparable F E]
  proof: by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have := expChar_of_injective_algebraMap (algebraMap F K).injective q
  refine linearIndependent_iff.mpr fun l hl => Finsupp.ext fun i => ?_
  choose f hf using fun i => (isPurelyInseparable_iff_pow_mem F q).1 ‹_› (l i)
  let n := l.support.sup f
  have := (ex

中文:
定理 LinearIndependent.map_of_isPurelyInseparable_of_isSeparable
  结论: [是纯不可分 F E]
  证明: by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have := expChar_of_injective_algebraMap (algebraMap F K).injective q
  refine linearIndependent_iff.mpr fun l hl => Finsupp.ext fun i => ?_
  choose f hf using fun i => (isPurelyInseparable_iff_pow_mem F q).1 ‹_› (l i)
  let n := l.support.sup f
  have := (ex

Depends on / 依赖: ExpChar, ExpChar.exists, Finsupp, Finsupp.ext, Nat.add, algebraMap, convert, expChar_of_injective_algebraMap, expChar_pow_pos, injective, isPurelyInseparable_iff_pow_mem, l.support, l.support.sup, linearIndependent_iff, linearIndependent_iff.mpr, pow_add, pow_mem, pow_mul, replace, support
-/
theorem LinearIndependent.map_of_isPurelyInseparable_of_isSeparable [IsPurelyInseparable F E]
    {ι : Type*} {v : ι -> K} (hsep : forall i : ι, IsSeparable F (v i))
    (h : LinearIndependent F v) : LinearIndependent E v := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have := expChar_of_injective_algebraMap (algebraMap F K).injective q
  refine linearIndependent_iff.mpr fun l hl => Finsupp.ext fun i => ?_
  choose f hf using fun i => (isPurelyInseparable_iff_pow_mem F q).1 ‹_› (l i)
  let n := l.support.sup f
  have := (expChar_pow_pos F q n).ne'
  replace hf (i : ι) : l i ^ q ^ n in (algebraMap F E).range := by
    by_cases hs : i in l.support
    · convert! pow_mem (hf i) (q ^ (n - f i)) using 1
      rw [← pow_mul]; rw [← pow_add]; rw [Nat.add_sub_of_le (Finset.le_sup hs)]
    exact ⟨0, by rw [map_zero, Finsupp.notMem_support_iff.1 hs, zero_pow this]⟩
  choose lF hlF using hf
  let lF₀ := Finsupp.onFinset l.support lF fun i => by
    contrapose
    refine fun hs => (injective_iff_map_eq_zero _).mp (algebraMap F E).injective _ ?_
    rw [hlF]; rw [Finsupp.notMem_support_iff.1 hs]; rw [zero_pow this]
replace h := linearIndependent_iff.1 (h.map_pow_expChar_pow_of_isSeparable' q n hsep :) lF₀ by
    replace hl := congr($hl ^ q ^ n)
    rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [sum_pow_char_pow]; rw [zero_pow this] at hl
    rw [← hl]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.onFinset_sum _ (fun _ => by exact zero_smul _ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [Algebra.smul_def, mul_pow, IsScalarTower.algebraMap_apply F E K, hlF, map_pow]
  refine eq_zero_of_pow_eq_zero ((hlF _).symm.trans ?_)
  convert! map_zero (algebraMap F E)
  exact congr($h i)

variable {F K} in
/--
theorem `IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable` / 定理 `IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable`

English:
theorem IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable
  proof: have ⟨ι, ⟨b⟩⟩ := Module.Basis.exists_basis F S
.of_basis_left b b.linearIndependent.map' S.val.toLinearMap
    (LinearMap.ker_eq_bot_of_injective S.val.injective)
.map_of_isPurelyInseparable_of_isSeparable E fun i => by
      simpa only [IsSeparable, minpoly_eq] using! Algebra.IsSeparable.isSeparabl

中文:
定理 中间域.linearDisjoint_of_isPurelyInseparable_of_isSeparable
  证明: have ⟨ι, ⟨b⟩⟩ := Module.Basis.exists_basis F S
.of_basis_left b b.linearIndependent.map' S.val.toLinearMap
    (LinearMap.ker_eq_bot_of_injective S.val.injective)
.map_of_isPurelyInseparable_of_isSeparable E fun i => by
      simpa only [IsSeparable, minpoly_eq] using! Algebra.IsSeparable.isSeparabl

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, LinearMap, LinearMap.ker_eq_bot_of_injective, Module, Module.Basis.exists_basis, S.val.injective, S.val.toLinearMap, b.linearIndependent.map, exists_basis, injective, isSeparable, ker_eq_bot_of_injective, linearIndependent, map_of_isPurelyInseparable_of_isSeparable, minpoly_eq, of_basis_left, toLinearMap
-/
theorem IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable
    [IsPurelyInseparable F E] (S : IntermediateField F K) [Algebra.IsSeparable F S] :
    S.LinearDisjoint E :=
  have ⟨ι, ⟨b⟩⟩ := Module.Basis.exists_basis F S
.of_basis_left b b.linearIndependent.map' S.val.toLinearMap
    (LinearMap.ker_eq_bot_of_injective S.val.injective)
.map_of_isPurelyInseparable_of_isSeparable E fun i => by
      simpa only [IsSeparable, minpoly_eq] using! Algebra.IsSeparable.isSeparable F (b i)

namespace Field

/--
lemma `sepDegree_eq_of_isPurelyInseparable_of_isSeparable` / 引理 `sepDegree_eq_of_isPurelyInseparable_of_isSeparable`

English:
lemma sepDegree_eq_of_isPurelyInseparable_of_isSeparable
  proof: by
  have h := (separableClosure F K).linearDisjoint_of_isPurelyInseparable_of_isSeparable E
.symm .adjoin_rank_eq_rank_left_of_isAlgebraic_left
  rwa [separableClosure.adjoin_eq_of_isAlgebraic_of_isSeparable K, rank_top'] at h

中文:
引理 sepDegree_eq_of_isPurelyInseparable_of_isSeparable
  证明: by
  have h := (separableClosure F K).linearDisjoint_of_isPurelyInseparable_of_isSeparable E
.symm .adjoin_rank_eq_rank_left_of_isAlgebraic_left
  rwa [separableClosure.adjoin_eq_of_isAlgebraic_of_isSeparable K, rank_top'] at h

Depends on / 依赖: adjoin_eq_of_isAlgebraic_of_isSeparable, adjoin_rank_eq_rank_left_of_isAlgebraic_left, linearDisjoint_of_isPurelyInseparable_of_isSeparable, rank_top, separableClosure, separableClosure.adjoin_eq_of_isAlgebraic_of_isSeparable
-/
lemma sepDegree_eq_of_isPurelyInseparable_of_isSeparable
    [IsPurelyInseparable F E] [Algebra.IsSeparable E K] : sepDegree F K = Module.rank E K := by
  have h := (separableClosure F K).linearDisjoint_of_isPurelyInseparable_of_isSeparable E
.symm .adjoin_rank_eq_rank_left_of_isAlgebraic_left
  rwa [separableClosure.adjoin_eq_of_isAlgebraic_of_isSeparable K, rank_top'] at h

/--
lemma `lift_rank_mul_lift_sepDegree_of_isSeparable` / 引理 `lift_rank_mul_lift_sepDegree_of_isSeparable`

English:
lemma lift_rank_mul_lift_sepDegree_of_isSeparable
  given: [Algebra.IsSeparable F E]
  proof: by
  rw [sepDegree]; rw [sepDegree]; rw [separableClosure.eq_restrictScalars_of_isSeparable F E K]
  exact lift_rank_mul_lift_rank F E (separableClosure E K)

中文:
引理 lift_rank_mul_lift_sepDegree_of_isSeparable
  条件: [代数.是可分 F E]
  证明: by
  rw [sepDegree]; rw [sepDegree]; rw [separableClosure.eq_restrictScalars_of_isSeparable F E K]
  exact lift_rank_mul_lift_rank F E (separableClosure E K)

Depends on / 依赖: eq_restrictScalars_of_isSeparable, lift_rank_mul_lift_rank, sepDegree, separableClosure, separableClosure.eq_restrictScalars_of_isSeparable
-/
lemma lift_rank_mul_lift_sepDegree_of_isSeparable [Algebra.IsSeparable F E] :
    Cardinal.lift.{w} (Module.rank F E) * Cardinal.lift.{v} (sepDegree E K) =
    Cardinal.lift.{v} (sepDegree F K) := by
  rw [sepDegree]; rw [sepDegree]; rw [separableClosure.eq_restrictScalars_of_isSeparable F E K]
  exact lift_rank_mul_lift_rank F E (separableClosure E K)

/--
lemma `rank_mul_sepDegree_of_isSeparable` / 引理 `rank_mul_sepDegree_of_isSeparable`

English:
lemma rank_mul_sepDegree_of_isSeparable
  statement: (K : Type v) [Field K] [Algebra F K]
  proof: by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_sepDegree_of_isSeparable F E K

中文:
引理 rank_mul_sepDegree_of_isSeparable
  结论: (K : 类型v) [域 K] [代数 F K]
  证明: by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_sepDegree_of_isSeparable F E K

Depends on / 依赖: Cardinal, Cardinal.lift_id, lift_id, lift_rank_mul_lift_sepDegree_of_isSeparable
-/
lemma rank_mul_sepDegree_of_isSeparable (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsSeparable F E] :
    Module.rank F E * sepDegree E K = sepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_sepDegree_of_isSeparable F E K

/--
lemma `insepDegree_eq_of_isSeparable` / 引理 `insepDegree_eq_of_isSeparable`

English:
lemma insepDegree_eq_of_isSeparable
  given: [Algebra.IsSeparable F E]
  proof: by
  rw [insepDegree]; rw [insepDegree]; rw [separableClosure.eq_restrictScalars_of_isSeparable F E K]
  rfl

中文:
引理 insepDegree_eq_of_isSeparable
  条件: [代数.是可分 F E]
  证明: by
  rw [insepDegree]; rw [insepDegree]; rw [separableClosure.eq_restrictScalars_of_isSeparable F E K]
  rfl

Depends on / 依赖: eq_restrictScalars_of_isSeparable, insepDegree, separableClosure, separableClosure.eq_restrictScalars_of_isSeparable
-/
lemma insepDegree_eq_of_isSeparable [Algebra.IsSeparable F E] :
    insepDegree F K = insepDegree E K := by
  rw [insepDegree]; rw [insepDegree]; rw [separableClosure.eq_restrictScalars_of_isSeparable F E K]
  rfl

/--
lemma `sepDegree_eq_of_isPurelyInseparable` / 引理 `sepDegree_eq_of_isPurelyInseparable`

English:
lemma sepDegree_eq_of_isPurelyInseparable
  given: [IsPurelyInseparable F E]
  proof: by
  convert! sepDegree_eq_of_isPurelyInseparable_of_isSeparable F E (separableClosure E K)
  have : IsScalarTower F (separableClosure E K) K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [sepDegree]; rw [← separableClosure.map_eq_of_separableClosure_eq_bot F
    (separableClosure.separableC

中文:
引理 sepDegree_eq_of_isPurelyInseparable
  条件: [是纯不可分 F E]
  证明: by
  convert! sepDegree_eq_of_isPurelyInseparable_of_isSeparable F E (separableClosure E K)
  have : IsScalarTower F (separableClosure E K) K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [sepDegree]; rw [← separableClosure.map_eq_of_separableClosure_eq_bot F
    (separableClosure.separableC

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, IsScalarTower.toAlgHom, convert, equivMap, map_eq_of_separableClosure_eq_bot, of_algebraMap_eq, rank_eq, sepDegree, sepDegree_eq_of_isPurelyInseparable_of_isSeparable, separableClosure, separableClosure.map_eq_of_separableClosure_eq_bot, separableClosure.separableClosure_eq_bot, separableClosure_eq_bot, symm.toLinearEquiv.rank_eq, toAlgHom, toLinearEquiv
-/
lemma sepDegree_eq_of_isPurelyInseparable [IsPurelyInseparable F E] :
    sepDegree F K = sepDegree E K := by
  convert! sepDegree_eq_of_isPurelyInseparable_of_isSeparable F E (separableClosure E K)
  have : IsScalarTower F (separableClosure E K) K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [sepDegree]; rw [← separableClosure.map_eq_of_separableClosure_eq_bot F
    (separableClosure.separableClosure_eq_bot E K)]
  exact (separableClosure F (separableClosure E K)).equivMap
.symm.toLinearEquiv.rank_eq (IsScalarTower.toAlgHom F (separableClosure E K) K)

/--
lemma `lift_rank_mul_lift_insepDegree_of_isPurelyInseparable` / 引理 `lift_rank_mul_lift_insepDegree_of_isPurelyInseparable`

English:
lemma lift_rank_mul_lift_insepDegree_of_isPurelyInseparable
  given: [IsPurelyInseparable F E]
  proof: by
  have h := (separableClosure F K).linearDisjoint_of_isPurelyInseparable_of_isSeparable E
.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left
  rwa [separableClosure.adjoin_eq_of_isAlgebraic] at h

中文:
引理 lift_rank_mul_lift_insepDegree_of_isPurelyInseparable
  条件: [是纯不可分 F E]
  证明: by
  have h := (separableClosure F K).linearDisjoint_of_isPurelyInseparable_of_isSeparable E
.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left
  rwa [separableClosure.adjoin_eq_of_isAlgebraic] at h

Depends on / 依赖: adjoin_eq_of_isAlgebraic, lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left, linearDisjoint_of_isPurelyInseparable_of_isSeparable, separableClosure, separableClosure.adjoin_eq_of_isAlgebraic
-/
lemma lift_rank_mul_lift_insepDegree_of_isPurelyInseparable [IsPurelyInseparable F E] :
    Cardinal.lift.{w} (Module.rank F E) * Cardinal.lift.{v} (insepDegree E K) =
    Cardinal.lift.{v} (insepDegree F K) := by
  have h := (separableClosure F K).linearDisjoint_of_isPurelyInseparable_of_isSeparable E
.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left
  rwa [separableClosure.adjoin_eq_of_isAlgebraic] at h

/--
lemma `rank_mul_insepDegree_of_isPurelyInseparable` / 引理 `rank_mul_insepDegree_of_isPurelyInseparable`

English:
lemma rank_mul_insepDegree_of_isPurelyInseparable
  statement: (K : Type v) [Field K] [Algebra F K]
  proof: by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_insepDegree_of_isPurelyInseparable F E K

中文:
引理 rank_mul_insepDegree_of_isPurelyInseparable
  结论: (K : 类型v) [域 K] [代数 F K]
  证明: by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_insepDegree_of_isPurelyInseparable F E K

Depends on / 依赖: Cardinal, Cardinal.lift_id, lift_id, lift_rank_mul_lift_insepDegree_of_isPurelyInseparable
-/
lemma rank_mul_insepDegree_of_isPurelyInseparable (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [IsPurelyInseparable F E] :
    Module.rank F E * insepDegree E K = insepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_insepDegree_of_isPurelyInseparable F E K

/--
theorem `lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic` / 定理 `lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`

English:
theorem lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic
  given: [Algebra.IsAlgebraic F E]
  proof: by
  have h := lift_rank_mul_lift_sepDegree_of_isSeparable F (separableClosure F E) K
  rwa [sepDegree_eq_of_isPurelyInseparable (separableClosure F E) E K] at h

中文:
定理 lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic
  条件: [代数.是代数 F E]
  证明: by
  have h := lift_rank_mul_lift_sepDegree_of_isSeparable F (separableClosure F E) K
  rwa [sepDegree_eq_of_isPurelyInseparable (separableClosure F E) E K] at h

Depends on / 依赖: lift_rank_mul_lift_sepDegree_of_isSeparable, sepDegree_eq_of_isPurelyInseparable, separableClosure
-/
theorem lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    Cardinal.lift.{w} (sepDegree F E) * Cardinal.lift.{v} (sepDegree E K) =
    Cardinal.lift.{v} (sepDegree F K) := by
  have h := lift_rank_mul_lift_sepDegree_of_isSeparable F (separableClosure F E) K
  rwa [sepDegree_eq_of_isPurelyInseparable (separableClosure F E) E K] at h

/-- The same-universe version of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`. -/
@[stacks 09HK "Part 1"]
/--
theorem `sepDegree_mul_sepDegree_of_isAlgebraic` / 定理 `sepDegree_mul_sepDegree_of_isAlgebraic`

English:
theorem sepDegree_mul_sepDegree_of_isAlgebraic
  statement: (K : Type v) [Field K] [Algebra F K]
  proof: by
  simpa only [Cardinal.lift_id] using lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic F E K

中文:
定理 sepDegree_mul_sepDegree_of_isAlgebraic
  结论: (K : 类型v) [域 K] [代数 F K]
  证明: by
  simpa only [Cardinal.lift_id] using lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic F E K

Depends on / 依赖: Cardinal, Cardinal.lift_id, lift_id, lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic
-/
theorem sepDegree_mul_sepDegree_of_isAlgebraic (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic F E] :
    sepDegree F E * sepDegree E K = sepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic F E K

/--
theorem `lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic` / 定理 `lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`

English:
theorem lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic
  given: [Algebra.IsAlgebraic F E]
  proof: by
  have h := lift_rank_mul_lift_insepDegree_of_isPurelyInseparable (separableClosure F E) E K
  rwa [← insepDegree_eq_of_isSeparable F (separableClosure F E) K] at h

中文:
定理 lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic
  条件: [代数.是代数 F E]
  证明: by
  have h := lift_rank_mul_lift_insepDegree_of_isPurelyInseparable (separableClosure F E) E K
  rwa [← insepDegree_eq_of_isSeparable F (separableClosure F E) K] at h

Depends on / 依赖: insepDegree_eq_of_isSeparable, lift_rank_mul_lift_insepDegree_of_isPurelyInseparable, separableClosure
-/
theorem lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    Cardinal.lift.{w} (insepDegree F E) * Cardinal.lift.{v} (insepDegree E K) =
    Cardinal.lift.{v} (insepDegree F K) := by
  have h := lift_rank_mul_lift_insepDegree_of_isPurelyInseparable (separableClosure F E) E K
  rwa [← insepDegree_eq_of_isSeparable F (separableClosure F E) K] at h

/-- The same-universe version of `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`. -/
@[stacks 09HK "Part 2"]
/--
theorem `insepDegree_mul_insepDegree_of_isAlgebraic` / 定理 `insepDegree_mul_insepDegree_of_isAlgebraic`

English:
theorem insepDegree_mul_insepDegree_of_isAlgebraic
  statement: (K : Type v) [Field K] [Algebra F K]
  proof: by
  simpa only [Cardinal.lift_id] using lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic F E K

中文:
定理 insepDegree_mul_insepDegree_of_isAlgebraic
  结论: (K : 类型v) [域 K] [代数 F K]
  证明: by
  simpa only [Cardinal.lift_id] using lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic F E K

Depends on / 依赖: Cardinal, Cardinal.lift_id, lift_id, lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic
-/
theorem insepDegree_mul_insepDegree_of_isAlgebraic (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic F E] :
    insepDegree F E * insepDegree E K = insepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic F E K

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then their
inseparable degrees, as natural numbers, satisfy the tower law: $[E:F]_i [K:E]_i = [K:F]_i$. -/
@[stacks 09HK "Part 2, `finInsepDegree` variant"]
/--
theorem `finInsepDegree_mul_finInsepDegree_of_isAlgebraic` / 定理 `finInsepDegree_mul_finInsepDegree_of_isAlgebraic`

English:
theorem finInsepDegree_mul_finInsepDegree_of_isAlgebraic
  given: [Algebra.IsAlgebraic F E]
  proof: by
  simpa only [map_mul, Cardinal.toNat_lift] using!
    congr(Cardinal.toNat $(lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic F E K))

中文:
定理 finInsepDegree_mul_finInsepDegree_of_isAlgebraic
  条件: [代数.是代数 F E]
  证明: by
  simpa only [map_mul, Cardinal.toNat_lift] using!
    congr(Cardinal.toNat $(lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic F E K))

Depends on / 依赖: Cardinal, Cardinal.toNat, Cardinal.toNat_lift, lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic, map_mul, toNat_lift
-/
theorem finInsepDegree_mul_finInsepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    finInsepDegree F E * finInsepDegree E K = finInsepDegree F K := by
  simpa only [map_mul, Cardinal.toNat_lift] using!
    congr(Cardinal.toNat $(lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic F E K))

end Field

variable {F K} in
/--
theorem `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable` / 定理 `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable`

English:
theorem IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable
  proof: by
  set M := adjoin F S
  set L := adjoin E S
  let E' := (IsScalarTower.toAlgHom F E K).fieldRange
  let j : E ≃ₐ[F] E' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K)
  have hi : M <= L.restrictScalars F := by
    rw [restrictScalars_adjoin_of_algEquiv (E := K) j rfl]; rw [restrictSca

中文:
定理 中间域.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable
  证明: by
  set M := adjoin F S
  set L := adjoin E S
  let E' := (IsScalarTower.toAlgHom F E K).fieldRange
  let j : E ≃ₐ[F] E' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K)
  have hi : M <= L.restrictScalars F := by
    rw [restrictScalars_adjoin_of_algEquiv (E := K) j rfl]; rw [restrictSca

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, Algebra, Algebra.toSMul, IsScalarTower, IsScalarTower.toAlgHom, L.restrictScalars, Set.subset_union_right, Subsemiring, Subsemiring.inclusion, adjoin, adjoin.mono, fieldRange, i.toAlgebra, inclusion, ofInjectiveField, restrictScalars, restrictScalars_adjoin, restrictScalars_adjoin_of_algEquiv, subset_union_right
-/
theorem IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable
    (S : Set K) [Algebra.IsAlgebraic F (adjoin F S)] [IsPurelyInseparable F E] :
    sepDegree E (adjoin E S) = sepDegree F (adjoin F S) := by
  set M := adjoin F S
  set L := adjoin E S
  let E' := (IsScalarTower.toAlgHom F E K).fieldRange
  let j : E ≃ₐ[F] E' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K)
  have hi : M <= L.restrictScalars F := by
    rw [restrictScalars_adjoin_of_algEquiv (E := K) j rfl]; rw [restrictScalars_adjoin]
    exact adjoin.mono _ _ _ Set.subset_union_right
  let i : M ->+* L := Subsemiring.inclusion hi
  let : Algebra M L := i.toAlgebra
  let : SMul M L := Algebra.toSMul
  have : IsScalarTower F M L := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  have : IsPurelyInseparable M L := by
    change IsPurelyInseparable M (extendScalars hi)
    obtain ⟨q, _⟩ := ExpChar.exists F
have : extendScalars hi = adjoin M (E' : Set K) := restrictScalars_injective F by
      conv_lhs => rw [extendScalars_restrictScalars, restrictScalars_adjoin_of_algEquiv
        (E := K) j rfl, ← adjoin_self F E', adjoin_adjoin_comm]
    rw [this]; rw [isPurelyInseparable_adjoin_iff_pow_mem _ _ q]
    rintro x ⟨y, hy⟩
    obtain ⟨n, z, hz⟩ := IsPurelyInseparable.pow_mem F q y
    refine ⟨n, algebraMap F M z, ?_⟩
    rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply F E K]; rw [hz]; rw [← hy]; rw [map_pow]; rw [AlgHom.toRingHom_eq_coe]; rw [IsScalarTower.coe_toAlgHom]
  have h := lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic F E L
  rw [IsPurelyInseparable.sepDegree_eq_one F E]; rw [Cardinal.lift_one]; rw [one_mul] at h
  rw [Cardinal.lift_injective h]; rw [← sepDegree_mul_sepDegree_of_isAlgebraic F M L]; rw [IsPurelyInseparable.sepDegree_eq_one M L]; rw [mul_one]

variable {F K} in
/--
theorem `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'` / 定理 `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'`

English:
theorem IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'
  proof: by
  have : Algebra.IsAlgebraic F (adjoin F (S : Set K)) := by rwa [adjoin_self]
  have := sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable (F := F) E (S : Set K)
  rwa [adjoin_self] at this

中文:
定理 中间域.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'
  证明: by
  have : Algebra.IsAlgebraic F (adjoin F (S : Set K)) := by rwa [adjoin_self]
  have := sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable (F := F) E (S : Set K)
  rwa [adjoin_self] at this

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, IsAlgebraic, adjoin, adjoin_self, sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable
-/
theorem IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'
    (S : IntermediateField F K) [Algebra.IsAlgebraic F S] [IsPurelyInseparable F E] :
    sepDegree E (adjoin E (S : Set K)) = sepDegree F S := by
  have : Algebra.IsAlgebraic F (adjoin F (S : Set K)) := by rwa [adjoin_self]
  have := sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable (F := F) E (S : Set K)
  rwa [adjoin_self] at this

variable {F K} in
/--
theorem `minpoly.map_eq_of_isSeparable_of_isPurelyInseparable` / 定理 `minpoly.map_eq_of_isSeparable_of_isPurelyInseparable`

English:
theorem minpoly.map_eq_of_isSeparable_of_isPurelyInseparable
  statement: (x : K)
  proof: by
  have hi := IsSeparable.isIntegral hsep
  have hi' : IsIntegral E x := IsIntegral.tower_top hi
  refine eq_of_monic_of_dvd_of_natDegree_le (monic hi') ((monic hi).map (algebraMap F E))
    (dvd_map_of_isScalarTower F E x) (le_of_eq ?_)
  have hsep' := IsSeparable.tower_top E hsep
  have := (isSe

中文:
定理 minpoly.map_eq_of_isSeparable_of_isPurelyInseparable
  结论: (x : K)
  证明: by
  have hi := IsSeparable.isIntegral hsep
  have hi' : IsIntegral E x := IsIntegral.tower_top hi
  refine eq_of_monic_of_dvd_of_natDegree_le (monic hi') ((monic hi).map (algebraMap F E))
    (dvd_map_of_isScalarTower F E x) (le_of_eq ?_)
  have hsep' := IsSeparable.tower_top E hsep
  have := (isSe

Depends on / 依赖: Algebra, Algebra.IsSeparable.isAlgebraic, IsIntegral, IsIntegral.tower_top, IsSeparable, IsSeparable.isIntegral, IsSeparable.tower_top, Polynomial, Polynomial.natDegree_map, adjoin, adjoin.finrank, algebraMap, dvd_map_of_isScalarTower, eq_of_monic_of_dvd_of_natDegree_le, finrank, isAlgebraic, isIntegral, isSeparable_adjoin_simple_iff_isSeparable, le_of_eq, natDegree_map
-/
theorem minpoly.map_eq_of_isSeparable_of_isPurelyInseparable (x : K)
    (hsep : IsSeparable F x) [IsPurelyInseparable F E] :
    (minpoly F x).map (algebraMap F E) = minpoly E x := by
  have hi := IsSeparable.isIntegral hsep
  have hi' : IsIntegral E x := IsIntegral.tower_top hi
  refine eq_of_monic_of_dvd_of_natDegree_le (monic hi') ((monic hi).map (algebraMap F E))
    (dvd_map_of_isScalarTower F E x) (le_of_eq ?_)
  have hsep' := IsSeparable.tower_top E hsep
  have := (isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsep
  have := (isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsep'
  have := Algebra.IsSeparable.isAlgebraic F F⟮x⟯
  rw [Polynomial.natDegree_map]; rw [← adjoin.finrank hi]; rw [← adjoin.finrank hi']; rw [← finSepDegree_eq_finrank_of_isSeparable F _]; rw [← finSepDegree_eq_finrank_of_isSeparable E _]; rw [finSepDegree_eq]; rw [finSepDegree_eq]; rw [sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable (F := F) E]

variable {F} in
/--
theorem `Polynomial.Separable.map_irreducible_of_isPurelyInseparable` / 定理 `Polynomial.Separable.map_irreducible_of_isPurelyInseparable`

English:
theorem Polynomial.Separable.map_irreducible_of_isPurelyInseparable
  statement: {f : F[X]} (hsep : f.Separable)
  proof: by
  let K := AlgebraicClosure E
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero K f
    (natDegree_pos_iff_degree_pos.1 hirr.natDegree_pos).ne'
  have ha : Associated f (minpoly F x) := by
    have := isUnit_C.2 (leadingCoeff_ne_zero.2 hirr.ne_zero).isUnit.inv
    exact ⟨this.unit, by rw [IsUn

中文:
定理 多项式.可分.map_irreducible_of_isPurelyInseparable
  结论: {f : F[X]} (hsep : f.可分)
  证明: by
  let K := AlgebraicClosure E
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero K f
    (natDegree_pos_iff_degree_pos.1 hirr.natDegree_pos).ne'
  have ha : Associated f (minpoly F x) := by
    have := isUnit_C.2 (leadingCoeff_ne_zero.2 hirr.ne_zero).isUnit.inv
    exact ⟨this.unit, by rw [IsUn

Depends on / 依赖: AlgebraicClosure, Associated, IsAlgClosed, IsAlgClosed.exists_aeval_eq_zero, IsUnit, IsUnit.unit_spec, algebraMap, eq_of_irreducible, exists_aeval_eq_zero, f.map, ha.map, hirr.natDegree_pos, hirr.ne_zero, isUnit, isUnit.inv, isUnit_C, leadingCoeff_ne_zero, mapRingHom, map_eq_of_is, minpoly
-/
theorem Polynomial.Separable.map_irreducible_of_isPurelyInseparable {f : F[X]} (hsep : f.Separable)
    (hirr : Irreducible f) [IsPurelyInseparable F E] : Irreducible (f.map (algebraMap F E)) := by
  let K := AlgebraicClosure E
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero K f
    (natDegree_pos_iff_degree_pos.1 hirr.natDegree_pos).ne'
  have ha : Associated f (minpoly F x) := by
    have := isUnit_C.2 (leadingCoeff_ne_zero.2 hirr.ne_zero).isUnit.inv
    exact ⟨this.unit, by rw [IsUnit.unit_spec, minpoly.eq_of_irreducible hirr hx]⟩
  have ha' : Associated (f.map (algebraMap F E)) ((minpoly F x).map (algebraMap F E)) :=
    ha.map (mapRingHom (algebraMap F E)).toMonoidHom
  have heq := minpoly.map_eq_of_isSeparable_of_isPurelyInseparable E x (ha.separable hsep)
  rw [ha'.irreducible_iff]; rw [heq]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral x)

end TowerLaw
