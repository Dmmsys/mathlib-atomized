/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Ralf Stephan
-/
module

public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.NumberTheory.Height.Northcott
public import Mathlib.NumberTheory.NumberField.ProductFormula

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Hom.Lattice
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Heights over number fields

We provide an instance of `Height.AdmissibleAbsValues` for algebraic number fields
and set up some API.

## Main results

* Heights on number fields satisfy the **Northcott property**: If `K` is a number field,
  then the set of elements of `K` of bounded (multiplicative or logarithmic) height is finite;
  see `NumberField.finite_setOfPred_mulHeight₁_le` and `NumberField.finite_setOfPred_logHeight₁_le`.
  We also provide instances for `Northcott (mulHeight₁ (K := K))` (which automatically leads
  also to `Northcott (logHeight₁ (K := K))`).

## TODO

When this file gets long, split the material on heights over `ℚ` off into a file `Rat.lean`.
-/

@[expose] public section

/-!
### Instance for number fields
-/

namespace NumberField

open Height

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/--
Definition of `multisetInfinitePlace` / `multisetInfinitePlace` 的定义

English:
definition multisetInfinitePlace
  signature: : Multiset (AbsoluteValue K Real)
  body: .bind (.univ : Finset (InfinitePlace K)).val fun v => .replicate v.mult v.val

@[simp]

中文:
定义 multisetInfinitePlace
  签名: : Multiset (AbsoluteValue K 实数)
  定义体: .bind (.univ : Finset (InfinitePlace K)).val fun v => .replicate v.mult v.val

@[simp]

Depends on / 依赖: Finset, InfinitePlace, replicate, v.mult, v.val
-/
noncomputable def multisetInfinitePlace : Multiset (AbsoluteValue K Real) :=
  .bind (.univ : Finset (InfinitePlace K)).val fun v => .replicate v.mult v.val

@[simp]
/--
lemma `mem_multisetInfinitePlace` / 引理 `mem_multisetInfinitePlace`

English:
lemma mem_multisetInfinitePlace
  given: {v : AbsoluteValue K Real}
  proof: by
  simp [multisetInfinitePlace, Multiset.mem_replicate, isInfinitePlace_iff, eq_comm (a := v)]

中文:
引理 mem_multisetInfinitePlace
  条件: {v : AbsoluteValue K 实数}
  证明: by
  simp [multisetInfinitePlace, Multiset.mem_replicate, isInfinitePlace_iff, eq_comm (a := v)]

Depends on / 依赖: Multiset, Multiset.mem_replicate, eq_comm, isInfinitePlace_iff, mem_replicate, multisetInfinitePlace
-/
lemma mem_multisetInfinitePlace {v : AbsoluteValue K Real} :
    v in multisetInfinitePlace K ↔ IsInfinitePlace v := by
  simp [multisetInfinitePlace, Multiset.mem_replicate, isInfinitePlace_iff, eq_comm (a := v)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `count_multisetInfinitePlace_eq_mult` / 引理 `count_multisetInfinitePlace_eq_mult`

English:
lemma count_multisetInfinitePlace_eq_mult
  given: [DecidableEq (AbsoluteValue K Real)] (v : InfinitePlace K)
  proof: by
  have : DecidableEq (InfinitePlace K) := Subtype.instDecidableEq
  simpa only [multisetInfinitePlace, Multiset.count_bind, Finset.sum_map_val,
    Multiset.count_replicate, ← Subtype.ext_iff] using Fintype.sum_ite_eq' v ..

中文:
引理 count_multisetInfinitePlace_eq_mult
  条件: [DecidableEq (AbsoluteValue K 实数)] (v : InfinitePlace K)
  证明: by
  have : DecidableEq (InfinitePlace K) := Subtype.instDecidableEq
  simpa only [multisetInfinitePlace, Multiset.count_bind, Finset.sum_map_val,
    Multiset.count_replicate, ← Subtype.ext_iff] using Fintype.sum_ite_eq' v ..

Depends on / 依赖: DecidableEq, Finset, Finset.sum_map_val, Fintype, Fintype.sum_ite_eq, InfinitePlace, Multiset, Multiset.count_bind, Multiset.count_replicate, Subtype, Subtype.ext_iff, Subtype.instDecidableEq, count_bind, count_replicate, ext_iff, instDecidableEq, multisetInfinitePlace, sum_ite_eq, sum_map_val
-/
lemma count_multisetInfinitePlace_eq_mult [DecidableEq (AbsoluteValue K Real)] (v : InfinitePlace K) :
    (multisetInfinitePlace K).count v.val = v.mult := by
  have : DecidableEq (InfinitePlace K) := Subtype.instDecidableEq
  simpa only [multisetInfinitePlace, Multiset.count_bind, Finset.sum_map_val,
    Multiset.count_replicate, ← Subtype.ext_iff] using Fintype.sum_ite_eq' v ..

set_option backward.isDefEq.respectTransparency.types false in
-- For the user-facing version, see `prod_archAbsVal_eq` below.
/--
lemma `prod_multisetInfinitePlace_eq` / 引理 `prod_multisetInfinitePlace_eq`

English:
lemma prod_multisetInfinitePlace_eq
  given: {M : Type*} [CommMonoid M] (f : AbsoluteValue K Real -> M)
  proof: by
  classical
  rw [Finset.prod_multiset_map_count]
  exact Finset.prod_bij' (fun w hw => ⟨w, mem_multisetInfinitePlace.mp <| Multiset.mem_dedup.mp hw⟩)
    (fun v _ => v.val) (fun _ _ => Finset.mem_univ _) (fun v _ => by simp [v.isInfinitePlace])
    (fun _ _ => rfl) (fun _ _ => rfl) fun w hw => b

中文:
引理 prod_multisetInfinitePlace_eq
  条件: {M : 类型} [CommMonoid M] (f : AbsoluteValue K 实数 -> M)
  证明: by
  classical
  rw [Finset.prod_multiset_map_count]
  exact Finset.prod_bij' (fun w hw => ⟨w, mem_multisetInfinitePlace.mp <| Multiset.mem_dedup.mp hw⟩)
    (fun v _ => v.val) (fun _ _ => Finset.mem_univ _) (fun v _ => by simp [v.isInfinitePlace])
    (fun _ _ => rfl) (fun _ _ => rfl) fun w hw => b
-/
private lemma prod_multisetInfinitePlace_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K Real -> M) :
    ((multisetInfinitePlace K).map f).prod = ∏ v : InfinitePlace K, f v.val ^ v.mult := by
  classical
  rw [Finset.prod_multiset_map_count]
  exact Finset.prod_bij' (fun w hw => ⟨w, mem_multisetInfinitePlace.mp <| Multiset.mem_dedup.mp hw⟩)
    (fun v _ => v.val) (fun _ _ => Finset.mem_univ _) (fun v _ => by simp [v.isInfinitePlace])
    (fun _ _ => rfl) (fun _ _ => rfl) fun w hw => by rw [count_multisetInfinitePlace_eq_mult ⟨w, _⟩]

noncomputable
/--
Instance `instAdmissibleAbsValues` / 实例 `instAdmissibleAbsValues`

English:
instance instAdmissibleAbsValues
  signature: : AdmissibleAbsValues K where
  body: multisetInfinitePlace K
  nonarchAbsVal := {v | IsFinitePlace v}
  isNonarchimedean v hv := FinitePlace.add_le ⟨v, by simpa using! hv⟩
  hasFiniteMulSupport := FinitePlace.hasFiniteMulSupport
  product_formula {x} hx := private prod_multisetInfinitePlace_eq (· x) ▸ prod_abs_eq_one hx

中文:
实例 instAdmissibleAbsValues
  签名: : AdmissibleAbsValues K where
  定义体: multisetInfinitePlace K
  nonarchAbsVal := {v | IsFinitePlace v}
  isNonarchimedean v hv := FinitePlace.add_le ⟨v, by simpa using! hv⟩
  hasFiniteMulSupport := FinitePlace.hasFiniteMulSupport
  product_formula {x} hx := private prod_multisetInfinitePlace_eq (· x) ▸ prod_abs_eq_one hx

Depends on / 依赖: multisetInfinitePlace
-/
instance instAdmissibleAbsValues : AdmissibleAbsValues K where
  archAbsVal := multisetInfinitePlace K
  nonarchAbsVal := {v | IsFinitePlace v}
  isNonarchimedean v hv := FinitePlace.add_le ⟨v, by simpa using! hv⟩
  hasFiniteMulSupport := FinitePlace.hasFiniteMulSupport
  product_formula {x} hx := private prod_multisetInfinitePlace_eq (· x) ▸ prod_abs_eq_one hx

open AdmissibleAbsValues

/--
lemma `prod_archAbsVal_eq` / 引理 `prod_archAbsVal_eq`

English:
lemma prod_archAbsVal_eq
  given: {M : Type*} [CommMonoid M] (f : AbsoluteValue K Real -> M)
  proof: prod_multisetInfinitePlace_eq f

中文:
引理 prod_archAbsVal_eq
  条件: {M : 类型} [CommMonoid M] (f : AbsoluteValue K 实数 -> M)
  证明: prod_multisetInfinitePlace_eq f

Depends on / 依赖: prod_multisetInfinitePlace_eq
-/
lemma prod_archAbsVal_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K Real -> M) :
    (archAbsVal.map f).prod = ∏ v : InfinitePlace K, f v.val ^ v.mult :=
  prod_multisetInfinitePlace_eq f

/--
lemma `prod_nonarchAbsVal_eq` / 引理 `prod_nonarchAbsVal_eq`

English:
lemma prod_nonarchAbsVal_eq
  given: {M : Type*} [CommMonoid M] (f : AbsoluteValue K Real -> M)
  proof: rfl

中文:
引理 prod_nonarchAbsVal_eq
  条件: {M : 类型} [CommMonoid M] (f : AbsoluteValue K 实数 -> M)
  证明: rfl
-/
lemma prod_nonarchAbsVal_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K Real -> M) :
    (∏ᶠ v : nonarchAbsVal, f v.val) = ∏ᶠ v : FinitePlace K, f v.val :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
open Finset Multiset in
/--
lemma `sum_archAbsVal_eq` / 引理 `sum_archAbsVal_eq`

English:
lemma sum_archAbsVal_eq
  given: {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K Real -> M)
  proof: by
  classical
  rw [sum_multiset_map_count]
  exact sum_bij' (⟨·, mem_multisetInfinitePlace.mp <| mem_dedup.mp ·⟩)
    _ (by simp) (by simp [InfinitePlace.isInfinitePlace, archAbsVal]) (by simp) (fun _ _ => rfl)
    fun w hw => by
      simp only [archAbsVal, mem_toFinset, mem_multisetInfinitePlace

中文:
引理 sum_archAbsVal_eq
  条件: {M : 类型} [AddCommMonoid M] (f : AbsoluteValue K 实数 -> M)
  证明: by
  classical
  rw [sum_multiset_map_count]
  exact sum_bij' (⟨·, mem_multisetInfinitePlace.mp <| mem_dedup.mp ·⟩)
    _ (by simp) (by simp [InfinitePlace.isInfinitePlace, archAbsVal]) (by simp) (fun _ _ => rfl)
    fun w hw => by
      simp only [archAbsVal, mem_toFinset, mem_multisetInfinitePlace

Depends on / 依赖: InfinitePlace, InfinitePlace.isInfinitePlace, archAbsVal, classical, count_multisetInfinitePlace_eq_mult, isInfinitePlace, mem_dedup, mem_dedup.mp, mem_multisetInfinitePlace, mem_multisetInfinitePlace.mp, mem_toFinset, sum_bij, sum_multiset_map_count
-/
lemma sum_archAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K Real -> M) :
    (archAbsVal.map f).sum = ∑ v : InfinitePlace K, v.mult • f v.val := by
  classical
  rw [sum_multiset_map_count]
  exact sum_bij' (⟨·, mem_multisetInfinitePlace.mp <| mem_dedup.mp ·⟩)
    _ (by simp) (by simp [InfinitePlace.isInfinitePlace, archAbsVal]) (by simp) (fun _ _ => rfl)
    fun w hw => by
      simp only [archAbsVal, mem_toFinset, mem_multisetInfinitePlace] at hw ⊢
      simp [count_multisetInfinitePlace_eq_mult ⟨w, hw⟩]

/--
lemma `sum_nonarchAbsVal_eq` / 引理 `sum_nonarchAbsVal_eq`

English:
lemma sum_nonarchAbsVal_eq
  given: {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K Real -> M)
  proof: rfl

中文:
引理 sum_nonarchAbsVal_eq
  条件: {M : 类型} [AddCommMonoid M] (f : AbsoluteValue K 实数 -> M)
  证明: rfl
-/
lemma sum_nonarchAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K Real -> M) :
    (∑ᶠ v : nonarchAbsVal, f v.val) = ∑ᶠ v : FinitePlace K, f v.val :=
  rfl

/--
lemma `mulHeight₁_eq` / 引理 `mulHeight₁_eq`

English:
lemma mulHeight₁_eq
  given: (x : K)
  proof: by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.mulHeight₁_eq,
    prod_archAbsVal_eq, prod_nonarchAbsVal_eq fun v => max (v x) 1]

中文:
引理 mulHeight₁_eq
  条件: (x : K)
  证明: by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.mulHeight₁_eq,
    prod_archAbsVal_eq, prod_nonarchAbsVal_eq fun v => max (v x) 1]

Depends on / 依赖: FinitePlace, FinitePlace.coe_apply, Height, Height.mulHeight, InfinitePlace, InfinitePlace.coe_apply, coe_apply, prod_archAbsVal_eq, prod_nonarchAbsVal_eq
-/
lemma mulHeight₁_eq (x : K) :
    mulHeight₁ x =
      (∏ v : InfinitePlace K, max (v x) 1 ^ v.mult) * ∏ᶠ v : FinitePlace K, max (v x) 1 := by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.mulHeight₁_eq,
    prod_archAbsVal_eq, prod_nonarchAbsVal_eq fun v => max (v x) 1]

open Real in
/--
lemma `logHeight₁_eq` / 引理 `logHeight₁_eq`

English:
lemma logHeight₁_eq
  given: (x : K)
  proof: by
  simp only [← nsmul_eq_mul, FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.logHeight₁_eq,
    sum_archAbsVal_eq, sum_nonarchAbsVal_eq fun v => log⁺ (v x)]

中文:
引理 logHeight₁_eq
  条件: (x : K)
  证明: by
  simp only [← nsmul_eq_mul, FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.logHeight₁_eq,
    sum_archAbsVal_eq, sum_nonarchAbsVal_eq fun v => log⁺ (v x)]

Depends on / 依赖: FinitePlace, FinitePlace.coe_apply, Height, Height.logHeight, InfinitePlace, InfinitePlace.coe_apply, coe_apply, nsmul_eq_mul, sum_archAbsVal_eq, sum_nonarchAbsVal_eq
-/
lemma logHeight₁_eq (x : K) :
    logHeight₁ x =
      (∑ v : InfinitePlace K, v.mult * log⁺ (v x)) + ∑ᶠ v : FinitePlace K, log⁺ (v x) := by
  simp only [← nsmul_eq_mul, FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.logHeight₁_eq,
    sum_archAbsVal_eq, sum_nonarchAbsVal_eq fun v => log⁺ (v x)]

/--
lemma `mulHeight_eq` / 引理 `mulHeight_eq`

English:
lemma mulHeight_eq
  given: {ι : Type*} {x : ι -> K} (hx : x != 0)
  proof: by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.mulHeight_eq hx,
    prod_archAbsVal_eq, prod_nonarchAbsVal_eq fun v => ⨆ i, v (x i)]

中文:
引理 mulHeight_eq
  条件: {ι : 类型} {x : ι -> K} (hx : x != 0)
  证明: by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.mulHeight_eq hx,
    prod_archAbsVal_eq, prod_nonarchAbsVal_eq fun v => ⨆ i, v (x i)]

Depends on / 依赖: FinitePlace, FinitePlace.coe_apply, Height, Height.mulHeight_eq, InfinitePlace, InfinitePlace.coe_apply, coe_apply, mulHeight_eq, prod_archAbsVal_eq, prod_nonarchAbsVal_eq
-/
lemma mulHeight_eq {ι : Type*} {x : ι -> K} (hx : x != 0) :
    mulHeight x =
      (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.mulHeight_eq hx,
    prod_archAbsVal_eq, prod_nonarchAbsVal_eq fun v => ⨆ i, v (x i)]

open Classical IntermediateField in
/--
Definition of `absMulHeight₁` / `absMulHeight₁` 的定义

English:
definition absMulHeight₁
  signature: {K : Type*} [Field K] [CharZero K] (x : K)
  body: if hx : IsIntegral Rat x then
    haveI : FiniteDimensional Rat Rat⟮x⟯ := adjoin.finiteDimensional hx
    haveI : NumberField Rat⟮x⟯ := {}
    (Height.mulHeight₁ (AdjoinSimple.gen Rat x)) ^ (Module.finrank Rat Rat⟮x⟯ : Real)⁻¹
  else 1

中文:
定义 absMulHeight₁
  签名: {K : 类型} [Field K] [CharZero K] (x : K)
  定义体: if hx : IsIntegral Rat x then
    haveI : FiniteDimensional Rat Rat⟮x⟯ := adjoin.finiteDimensional hx
    haveI : NumberField Rat⟮x⟯ := {}
    (Height.mulHeight₁ (AdjoinSimple.gen Rat x)) ^ (Module.finrank Rat Rat⟮x⟯ : Real)⁻¹
  else 1

Depends on / 依赖: AdjoinSimple, AdjoinSimple.gen, FiniteDimensional, Height, Height.mulHeight, IsIntegral, Module, Module.finrank, NumberField, adjoin, adjoin.finiteDimensional, finiteDimensional, finrank
-/
noncomputable def absMulHeight₁ {K : Type*} [Field K] [CharZero K] (x : K) : Real :=
  if hx : IsIntegral Rat x then
    haveI : FiniteDimensional Rat Rat⟮x⟯ := adjoin.finiteDimensional hx
    haveI : NumberField Rat⟮x⟯ := {}
    (Height.mulHeight₁ (AdjoinSimple.gen Rat x)) ^ (Module.finrank Rat Rat⟮x⟯ : Real)⁻¹
  else 1

/--
Definition of `absLogHeight₁` / `absLogHeight₁` 的定义

English:
definition absLogHeight₁
  signature: {K : Type*} [Field K] [CharZero K] (x : K)
  body: (absMulHeight₁ x).log

中文:
定义 absLogHeight₁
  签名: {K : 类型} [Field K] [CharZero K] (x : K)
  定义体: (absMulHeight₁ x).log
-/
noncomputable def absLogHeight₁ {K : Type*} [Field K] [CharZero K] (x : K) : Real :=
  (absMulHeight₁ x).log

variable (K) in
/--
lemma `totalWeight_eq_sum_mult` / 引理 `totalWeight_eq_sum_mult`

English:
lemma totalWeight_eq_sum_mult
  statement: totalWeight K = ∑ v : InfinitePlace K, v.mult
  proof: by
  simp only [totalWeight]
  convert! sum_archAbsVal_eq (fun _ => (1 : Nat))
  · rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem, ← Multiset.length_toList,
      Fin.sum_const, Multiset.length_toList, smul_eq_mul, mul_one]
  · simp

中文:
引理 totalWeight_eq_sum_mult
  结论: totalWeight K = ∑ v : InfinitePlace K, v.mult
  证明: by
  simp only [totalWeight]
  convert! sum_archAbsVal_eq (fun _ => (1 : Nat))
  · rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem, ← Multiset.length_toList,
      Fin.sum_const, Multiset.length_toList, smul_eq_mul, mul_one]
  · simp

Depends on / 依赖: Fin.sum_const, Fin.sum_univ_fun_getElem, Multiset, Multiset.length_toList, Multiset.sum_map_toList, convert, length_toList, mul_one, smul_eq_mul, sum_archAbsVal_eq, sum_const, sum_map_toList, sum_univ_fun_getElem, totalWeight
-/
lemma totalWeight_eq_sum_mult : totalWeight K = ∑ v : InfinitePlace K, v.mult := by
  simp only [totalWeight]
  convert! sum_archAbsVal_eq (fun _ => (1 : Nat))
  · rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem, ← Multiset.length_toList,
      Fin.sum_const, Multiset.length_toList, smul_eq_mul, mul_one]
  · simp

variable (K) in
/--
lemma `totalWeight_eq_finrank` / 引理 `totalWeight_eq_finrank`

English:
lemma totalWeight_eq_finrank
  statement: totalWeight K = Module.finrank Rat K
  proof: by
  rw [totalWeight_eq_sum_mult]; rw [InfinitePlace.sum_mult_eq]

中文:
引理 totalWeight_eq_finrank
  结论: totalWeight K = Module.finrank Rat K
  证明: by
  rw [totalWeight_eq_sum_mult]; rw [InfinitePlace.sum_mult_eq]

Depends on / 依赖: InfinitePlace, InfinitePlace.sum_mult_eq, sum_mult_eq, totalWeight_eq_sum_mult
-/
lemma totalWeight_eq_finrank : totalWeight K = Module.finrank Rat K := by
  rw [totalWeight_eq_sum_mult]; rw [InfinitePlace.sum_mult_eq]

variable (K) in
@[grind! .]
/--
lemma `totalWeight_pos` / 引理 `totalWeight_pos`

English:
lemma totalWeight_pos
  statement: 0 < totalWeight K
  proof: by
  have : Inhabited (InfinitePlace K) := Classical.inhabited_of_nonempty'
  simpa [totalWeight, archAbsVal, multisetInfinitePlace]
    using Fintype.sum_pos
      (Function.ne_iff.mpr ⟨default, (default : InfinitePlace K).mult_ne_zero⟩).pos

中文:
引理 totalWeight_pos
  结论: 0 < totalWeight K
  证明: by
  have : Inhabited (InfinitePlace K) := Classical.inhabited_of_nonempty'
  simpa [totalWeight, archAbsVal, multisetInfinitePlace]
    using Fintype.sum_pos
      (Function.ne_iff.mpr ⟨default, (default : InfinitePlace K).mult_ne_zero⟩).pos

Depends on / 依赖: Classical, Classical.inhabited_of_nonempty, Fintype, Fintype.sum_pos, Function, Function.ne_iff.mpr, InfinitePlace, Inhabited, archAbsVal, inhabited_of_nonempty, mult_ne_zero, multisetInfinitePlace, ne_iff, sum_pos, totalWeight
-/
lemma totalWeight_pos : 0 < totalWeight K := by
  have : Inhabited (InfinitePlace K) := Classical.inhabited_of_nonempty'
  simpa [totalWeight, archAbsVal, multisetInfinitePlace]
    using Fintype.sum_pos
      (Function.ne_iff.mpr ⟨default, (default : InfinitePlace K).mult_ne_zero⟩).pos

variable {ι : Type*} [Finite ι] {x : ι -> 𝓞 K}

open IsDedekindDomain.HeightOneSpectrum Ideal FinitePlace Finite in
-- This statement is a step in the proof of the next one, which is strictly stronger.
/--
lemma `absNorm_mul_finprod_finitePlace_eq_one_aux` / 引理 `absNorm_mul_finprod_finitePlace_eq_one_aux`

English:
lemma absNorm_mul_finprod_finitePlace_eq_one_aux
  given: [Nonempty ι] (hx : forall i, x i != 0)
  proof: by
  have H j : span {x j} != ⊥ := mt span_singleton_eq_bot.mp (hx j)
  have hx' : ⨆ i, span {x i} != ⊥ :=
iSup_eq_bot.not.mpr not_forall.mpr ⟨Classical.ofNonempty, H _⟩
  rw [span_range_eq_iSup]; rw [← finprod_finitePlace_pow_multiplicity hx']; rw [map_finprod _ hasFiniteMulSupport_fun_pow_multipli

中文:
引理 absNorm_mul_finprod_finitePlace_eq_one_aux
  条件: [Nonempty ι] (hx : 对任意 i, x i != 0)
  证明: by
  have H j : span {x j} != ⊥ := mt span_singleton_eq_bot.mp (hx j)
  have hx' : ⨆ i, span {x i} != ⊥ :=
iSup_eq_bot.not.mpr not_forall.mpr ⟨Classical.ofNonempty, H _⟩
  rw [span_range_eq_iSup]; rw [← finprod_finitePlace_pow_multiplicity hx']; rw [map_finprod _ hasFiniteMulSupport_fun_pow_multipli
-/
private lemma absNorm_mul_finprod_finitePlace_eq_one_aux [Nonempty ι] (hx : forall i, x i != 0) :
    (span <| Set.range x).absNorm * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) = 1 := by
  have H j : span {x j} != ⊥ := mt span_singleton_eq_bot.mp (hx j)
  have hx' : ⨆ i, span {x i} != ⊥ :=
iSup_eq_bot.not.mpr not_forall.mpr ⟨Classical.ofNonempty, H _⟩
  rw [span_range_eq_iSup]; rw [← finprod_finitePlace_pow_multiplicity hx']; rw [map_finprod _ hasFiniteMulSupport_fun_pow_multiplicity hx' (·)]; rw [Nat.cast_finprod']; rw [← finprod_mul_distrib ?hf .iSup (FinitePlace.hasFiniteMulSupport <| mod_cast hx ·)]
  case hf =>
    simp only [map_pow, Nat.cast_pow]
    exact hasFiniteMulSupport_fun_pow_multiplicity hx' fun v => (v.absNorm : Real)
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  have hn := absNorm_eq_zero_iff.not.mpr v.maximalIdeal.ne_bot
  have h {m : Nat} : (0 : Real) < ↑(absNorm v.maximalIdeal.asIdeal ^ m) := by positivity
  rw [multiplicity_iSup _ H]; rw [map_pow]; rw [mul_eq_one_iff_inv_eq₀ h.ne']; rw [map_iInf_of_monotone (fun _ => multiplicity ..) (pow_right_monotone <| by lia)]; rw [map_iInf_of_monotone _ Nat.mono_cast]; rw [map_iInf_of_antitoneOn antitoneOn_inv_pos fun _ => Set.mem_ofPred.mpr h]
  refine iSup_congr fun i => ?_
  rw [← mul_eq_one_iff_inv_eq₀ h.ne']; rw [mul_comm]; rw [Nat.cast_pow]
  exact apply_mul_absNorm_pow_eq_one v (hx i)

-- TODO: Generalize the following to integral closures of `ℤ` in `K` in place of `𝓞 K`.
open Ideal in
/--
lemma `absNorm_mul_finprod_finitePlace_eq_one` / 引理 `absNorm_mul_finprod_finitePlace_eq_one`

English:
lemma absNorm_mul_finprod_finitePlace_eq_one
  given: (hx : x != 0)
  proof: by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  let i' : { j // (x j : K) != 0 } := ⟨i₀, mod_cast hi₀⟩
  have : Nonempty _ := .intro i'
  have hI : span (Set.range x) = span (Set.range fun i : { j // (x j : K) != 0 } => x i.val) := by
    convert span_range_eq_span_range_support x <;> norm_cast
  h

中文:
引理 absNorm_mul_finprod_finitePlace_eq_one
  条件: (hx : x != 0)
  证明: by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  let i' : { j // (x j : K) != 0 } := ⟨i₀, mod_cast hi₀⟩
  have : Nonempty _ := .intro i'
  have hI : span (Set.range x) = span (Set.range fun i : { j // (x j : K) != 0 } => x i.val) := by
    convert span_range_eq_span_range_support x <;> norm_cast
  h

Depends on / 依赖: Finite, Finite.iSup_eq_iSup_subtype, Function, Function.ne_iff.mp, Function.ne_iff.mpr, Nonempty, Set.range, absNorm_mul_finprod_finitePlace_eq_one_aux, convert, i.val, iSup_eq_iSup_subtype, j.prop, mod_cast, ne_iff, simp_rw, span_range_eq_span_range_support
-/
lemma absNorm_mul_finprod_finitePlace_eq_one (hx : x != 0) :
    (span <| Set.range x).absNorm * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) = 1 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  let i' : { j // (x j : K) != 0 } := ⟨i₀, mod_cast hi₀⟩
  have : Nonempty _ := .intro i'
  have hI : span (Set.range x) = span (Set.range fun i : { j // (x j : K) != 0 } => x i.val) := by
    convert span_range_eq_span_range_support x <;> norm_cast
  have hx₀ : (fun i => (x i : K)) != 0 := Function.ne_iff.mpr ⟨_, i'.prop⟩
  simp_rw [Finite.iSup_eq_iSup_subtype hx₀, hI]
  exact absNorm_mul_finprod_finitePlace_eq_one_aux fun j => mod_cast j.prop

end NumberField

/-!
### The Northcott property for heights on number fields

We show that a number field `K` has the **Northcott property** with respect to the multiplicative
and with respect to the logarithmic height, i.e., for any `B : ℝ` the set of elements `x : K`
such that `mulHeight₁ x ≤ B` (resp., `logHeight₁ x ≤ B`) is finite.
See `NumberField.finite_setOfPred_mulHeight₁_le` and `NumberField.finite_setOfPred_logHeight₁_le`.

The main idea of the proof is as follows. We show that for every `x : K` there is `n : ℕ` such that
`n * x` is an algebraic integer and `n ≤ mulHeight₁ x`; see `NumberField.exists_nat_le_mulHeight₁`.
We also show that the set of `a : 𝓞 K` such that `mulHeight₁ (a / n)` is bounded is finite;
see `NumberField.finite_setOfPred_prod_infinitePlace_iSup_le`. The result for the multiplicative
height follows by combining these two ingredients, and the result for the logarithmic height follows
from that for any field with a family of admissible absolute values
(see `Mathlib.NumberTheory.Height.Northcott`).
-/

section Northcott

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

section withIdeal

open Ideal

/--
lemma `relIndex_span_span_nat_mul` / 引理 `relIndex_span_span_nat_mul`

English:
lemma relIndex_span_span_nat_mul
  given: (m : Nat) {n : Nat} (hn : n != 0) (a : 𝓞 K)
  proof: by
  let f : 𝓞 K ->ₗ[𝓞 K] 𝓞 K := .mulLeft _ n
  have hf : Function.Injective (f : 𝓞 K ->+ 𝓞 K) :=
    (injective_iff_map_eq_zero f).mpr fun _ _ => by simp_all [f]
  have H₁ : span {(n * m : 𝓞 K)} = Submodule.map f (span {↑m}) := by
    simp [LinearMap.map_span, f]
  have H₂ : span {↑(n * m), n * a} 

中文:
引理 relIndex_span_span_nat_mul
  条件: (m : 自然数) {n : 自然数} (hn : n != 0) (a : 𝓞 K)
  证明: by
  let f : 𝓞 K ->ₗ[𝓞 K] 𝓞 K := .mulLeft _ n
  have hf : Function.Injective (f : 𝓞 K ->+ 𝓞 K) :=
    (injective_iff_map_eq_zero f).mpr fun _ _ => by simp_all [f]
  have H₁ : span {(n * m : 𝓞 K)} = Submodule.map f (span {↑m}) := by
    simp [LinearMap.map_span, f]
  have H₂ : span {↑(n * m), n * a} 
-/
private lemma relIndex_span_span_nat_mul (m : Nat) {n : Nat} (hn : n != 0) (a : 𝓞 K) :
    (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑m, a}).toAddSubgroup =
      (span {(n * m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑(n * m), n * a}).toAddSubgroup := by
  let f : 𝓞 K ->ₗ[𝓞 K] 𝓞 K := .mulLeft _ n
  have hf : Function.Injective (f : 𝓞 K ->+ 𝓞 K) :=
    (injective_iff_map_eq_zero f).mpr fun _ _ => by simp_all [f]
  have H₁ : span {(n * m : 𝓞 K)} = Submodule.map f (span {↑m}) := by
    simp [LinearMap.map_span, f]
  have H₂ : span {↑(n * m), n * a} = Submodule.map f (span {↑m, a}) := by
    simp [LinearMap.map_span, f, Set.image_pair]
  rw [H₁]; rw [H₂]
.symm exact AddSubgroup.relIndex_map_map_of_injective _ _ hf

/--
lemma `relIndex_span_span_eq_relIndex_span_span` / 引理 `relIndex_span_span_eq_relIndex_span_span`

English:
lemma relIndex_span_span_eq_relIndex_span_span
  statement: {m n : Nat} (hm : m != 0) (hn : n != 0)
  proof: by
  refine (relIndex_span_span_nat_mul m hn a).trans ?_
  rw [mul_comm]; rw [mul_comm n]; rw [h]
  exact (relIndex_span_span_nat_mul n hm b).symm

中文:
引理 relIndex_span_span_eq_relIndex_span_span
  结论: {m n : 自然数} (hm : m != 0) (hn : n != 0)
  证明: by
  refine (relIndex_span_span_nat_mul m hn a).trans ?_
  rw [mul_comm]; rw [mul_comm n]; rw [h]
  exact (relIndex_span_span_nat_mul n hm b).symm
-/
private lemma relIndex_span_span_eq_relIndex_span_span {m n : Nat} (hm : m != 0) (hn : n != 0)
    {a b : 𝓞 K} (h : n * a = m * b) :
    (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑m, a}).toAddSubgroup =
      (span {(n : 𝓞 K)}).toAddSubgroup.relIndex (span {↑n, b}).toAddSubgroup := by
  refine (relIndex_span_span_nat_mul m hn a).trans ?_
  rw [mul_comm]; rw [mul_comm n]; rw [h]
  exact (relIndex_span_span_nat_mul n hm b).symm

open Module AddSubgroup LinearMap in
/--
lemma `exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow` / 引理 `exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow`

English:
lemma exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow
  given: (x : K)
  proof: by
.mpr (.of_finite Rat x) have hx : IsAlgebraic Int x := IsFractionRing.isAlgebraic_iff Int _ _
  obtain ⟨m, r, hm, hmr⟩ := hx.exists_nsmul_eq (𝓞 K)
  rw [← RingOfIntegers.coe_eq_algebraMap r] at hmr
  set n := (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {(m : 𝓞 K), r}).toAddSubgroup with hndef

中文:
引理 exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow
  条件: (x : K)
  证明: by
.mpr (.of_finite Rat x) have hx : IsAlgebraic Int x := IsFractionRing.isAlgebraic_iff Int _ _
  obtain ⟨m, r, hm, hmr⟩ := hx.exists_nsmul_eq (𝓞 K)
  rw [← RingOfIntegers.coe_eq_algebraMap r] at hmr
  set n := (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {(m : 𝓞 K), r}).toAddSubgroup with hndef

Depends on / 依赖: IsAlgebraic, IsFractionRing, IsFractionRing.isAlgebraic_iff, RingOfIntegers, RingOfIntegers.coe_eq_algebraMap, coe_eq_algebraMap, exists_nsmul_eq, hx.exists_nsmul_eq, isAlgebraic_iff, isFiniteRelIndex, nsmul_relIndex_m, of_finite, relIndex, relIndex_ne_zero, toAddSubgroup, toAddSubgroup.nsmul_relIndex_m, toAddSubgroup.relIndex
-/
lemma exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow (x : K) :
    exists n : Nat, n != 0 ∧ exists a : 𝓞 K, n * x = a ∧
      (span {(n : 𝓞 K), a}).absNorm = n ^ (Module.finrank Rat K - 1) := by
.mpr (.of_finite Rat x) have hx : IsAlgebraic Int x := IsFractionRing.isAlgebraic_iff Int _ _
  obtain ⟨m, r, hm, hmr⟩ := hx.exists_nsmul_eq (𝓞 K)
  rw [← RingOfIntegers.coe_eq_algebraMap r] at hmr
  set n := (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {(m : 𝓞 K), r}).toAddSubgroup with hndef
.relIndex_ne_zero have hn : n != 0 := isFiniteRelIndex (by simp [hm]) _
  obtain ⟨a, ha'⟩ : exists a, m * a = n * r := by
    have : n • r in span {(m : 𝓞 K)} :=
(span {(m : 𝓞 K)}).toAddSubgroup.nsmul_relIndex_mem Submodule.mem_span_of_mem by grind
    simpa [mem_span_singleton', mul_comm] using this
  have ha : n * x = a := by
    refine mul_left_cancel₀ (mod_cast hm : (m : K) != 0) ?_
    rw [mul_left_comm]; rw [← nsmul_eq_mul m]; rw [hmr]
    exact_mod_cast ha'.symm
  refine ⟨n, hn, a, ha, mul_left_cancel₀ hn ?_⟩
  nth_rewrite 1 [hndef]
  rw [absNorm_eq_index]; rw [mul_pow_sub_one finrank_pos.ne']; rw [← RingOfIntegers.rank]; rw [← absNorm_span_natCast]; rw [absNorm_eq_index]; rw [← relIndex_span_span_eq_relIndex_span_span hn hm ha']
exact relIndex_mul_index Submodule.toAddSubgroup_mono span_mono by grind

open Height in
/--
lemma `one_le_pow_totalWeight_mul_finprod` / 引理 `one_le_pow_totalWeight_mul_finprod`

English:
lemma one_le_pow_totalWeight_mul_finprod
  given: {n : Nat} (hn : n != 0) (a : 𝓞 K)
  proof: by
  have Hw : (0 : Real) < n ^ totalWeight K := by positivity
  rw_mod_cast [totalWeight_eq_finrank, ← RingOfIntegers.rank, ← absNorm_span_natCast] at Hw ⊢
  rw [← absNorm_mul_finprod_finitePlace_eq_one (show ![a]; rw [n] != 0 by simp [hn])]
  gcongr
  · exact finprod_nonneg fun _ => Real.iSup_nonn

中文:
引理 one_le_pow_totalWeight_mul_finprod
  条件: {n : 自然数} (hn : n != 0) (a : 𝓞 K)
  证明: by
  have Hw : (0 : Real) < n ^ totalWeight K := by positivity
  rw_mod_cast [totalWeight_eq_finrank, ← RingOfIntegers.rank, ← absNorm_span_natCast] at Hw ⊢
  rw [← absNorm_mul_finprod_finitePlace_eq_one (show ![a]; rw [n] != 0 by simp [hn])]
  gcongr
  · exact finprod_nonneg fun _ => Real.iSup_nonn
-/
private lemma one_le_pow_totalWeight_mul_finprod {n : Nat} (hn : n != 0) (a : 𝓞 K) :
    1 <= (n ^ totalWeight K : Real) * ∏ᶠ (v : FinitePlace K), ⨆ i, v (![↑a, ↑n] i) := by
  have Hw : (0 : Real) < n ^ totalWeight K := by positivity
  rw_mod_cast [totalWeight_eq_finrank, ← RingOfIntegers.rank, ← absNorm_span_natCast] at Hw ⊢
  rw [← absNorm_mul_finprod_finitePlace_eq_one (show ![a]; rw [n] != 0 by simp [hn])]
  gcongr
  · exact finprod_nonneg fun _ => Real.iSup_nonneg_of_nonnegHomClass ..
· exact Nat.le_of_dvd Hw absNorm_dvd_absNorm_of_le span_mono by simp
  · apply le_of_eq; congr; ext; congr; ext i; fin_cases i <;> simp

end withIdeal

open Height

section withFinset

open Finset

-- TODO: Use this to show `natDenominator x ≤ mulHeight₁ x` once #39872 is merged.
/--
lemma `exists_nat_le_mulHeight₁` / 引理 `exists_nat_le_mulHeight₁`

English:
lemma exists_nat_le_mulHeight₁
  given: (x : K)
  proof: by
  obtain ⟨n, hn, a, ha₁, ha₂⟩ := exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow x
  refine ⟨n, hn, ?_, ha₁ ▸ a.isIntegral_coe⟩
  rw [← totalWeight_eq_finrank] at ha₂
  have hv (i : Fin 2) : (![a, n] i : K) = ![(a : K), n] i := by fin_cases i <;> rfl
  rw [← mul_div_cancel_left₀ 

中文:
引理 exists_nat_le_mulHeight₁
  条件: (x : K)
  证明: by
  obtain ⟨n, hn, a, ha₁, ha₂⟩ := exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow x
  refine ⟨n, hn, ?_, ha₁ ▸ a.isIntegral_coe⟩
  rw [← totalWeight_eq_finrank] at ha₂
  have hv (i : Fin 2) : (![a, n] i : K) = ![(a : K), n] i := by fin_cases i <;> rfl
  rw [← mul_div_cancel_left₀ 

Depends on / 依赖: a.isIntegral_coe, exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow, fin_cases, isIntegral_coe, le_of_mul_le_mul_left, mod_cast, mulHeight_eq, totalWeight, totalWeight_eq_finrank
-/
lemma exists_nat_le_mulHeight₁ (x : K) :
    exists n : Nat, n != 0 ∧ n <= mulHeight₁ x ∧ IsIntegral Int (n * x) := by
  obtain ⟨n, hn, a, ha₁, ha₂⟩ := exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow x
  refine ⟨n, hn, ?_, ha₁ ▸ a.isIntegral_coe⟩
  rw [← totalWeight_eq_finrank] at ha₂
  have hv (i : Fin 2) : (![a, n] i : K) = ![(a : K), n] i := by fin_cases i <;> rfl
  rw [← mul_div_cancel_left₀ x (mod_cast hn : (n : K) != 0)]; rw [ha₁]; rw [mulHeight₁_div_eq_mulHeight]; rw [mulHeight_eq (by simp [hn])]
  refine le_of_mul_le_mul_left ?_ (show (0 : Real) < n ^ (totalWeight K - 1) by positivity)
  have : n ^ (totalWeight K - 1) * ∏ᶠ (v : FinitePlace K), ⨆ i, v (![(a : K), n] i) = 1 := by
    simpa [ha₂, hv] using absNorm_mul_finprod_finitePlace_eq_one (show ![a, n] != 0 by simp [hn])
  rw [pow_sub_one_mul (totalWeight_pos K).ne']; rw [mul_left_comm]; rw [this]; rw [mul_one]; rw [totalWeight_eq_sum_mult]; rw [← prod_pow_eq_pow_sum univ]
  gcongr
exact Finite.le_ciSup_of_le 1 by simp

/--
lemma `pow_totalWeight_sub_one_eq` / 引理 `pow_totalWeight_sub_one_eq`

English:
lemma pow_totalWeight_sub_one_eq
  statement: [DecidableEq (InfinitePlace K)] {n : Nat} (hn : n != 0)
  proof: by
  refine mul_right_cancel₀ (b := (n : Real)) (mod_cast hn) ?_
  rw [pow_sub_one_mul (totalWeight_pos K).ne']; rw [totalWeight_eq_sum_mult]; rw [← prod_pow_eq_pow_sum]; rw [← prod_erase_mul _ _ (mem_univ v)]; rw [← pow_sub_one_mul v.mult_ne_zero]; rw [← mul_assoc]

中文:
引理 pow_totalWeight_sub_one_eq
  结论: [DecidableEq (InfinitePlace K)] {n : 自然数} (hn : n != 0)
  证明: by
  refine mul_right_cancel₀ (b := (n : Real)) (mod_cast hn) ?_
  rw [pow_sub_one_mul (totalWeight_pos K).ne']; rw [totalWeight_eq_sum_mult]; rw [← prod_pow_eq_pow_sum]; rw [← prod_erase_mul _ _ (mem_univ v)]; rw [← pow_sub_one_mul v.mult_ne_zero]; rw [← mul_assoc]
-/
private lemma pow_totalWeight_sub_one_eq [DecidableEq (InfinitePlace K)] {n : Nat} (hn : n != 0)
    (v : InfinitePlace K) :
    (n ^ (totalWeight K - 1) : Real) = (∏ w in univ.erase v, (n ^ w.mult : Real)) * n ^ (v.mult - 1) := by
  refine mul_right_cancel₀ (b := (n : Real)) (mod_cast hn) ?_
  rw [pow_sub_one_mul (totalWeight_pos K).ne']; rw [totalWeight_eq_sum_mult]; rw [← prod_pow_eq_pow_sum]; rw [← prod_erase_mul _ _ (mem_univ v)]; rw [← pow_sub_one_mul v.mult_ne_zero]; rw [← mul_assoc]

/--
lemma `infinitePlace_apply_le_of_prod_le` / 引理 `infinitePlace_apply_le_of_prod_le`

English:
lemma infinitePlace_apply_le_of_prod_le
  statement: {n : Nat} (hn : n != 0) (B : Real) {x : 𝓞 K}
  proof: by
  classical
  rw [le_div_iff₀' (by positivity)]
  calc
    _ <= n ^ (totalWeight K - 1) * ⨆ i, v (![(x : K), n] i) := by
      gcongr; exact Finite.le_ciSup_of_le 0 le_rfl
    _ <= (∏ v' in univ.erase v, (⨆ i, v' (![↑x, ↑n] i)) ^ v'.mult) *
         (⨆ i, v (![↑x, ↑n] i)) ^ (v.mult - 1) * ⨆ i, v 

中文:
引理 infinitePlace_apply_le_of_prod_le
  结论: {n : 自然数} (hn : n != 0) (B : 实数) {x : 𝓞 K}
  证明: by
  classical
  rw [le_div_iff₀' (by positivity)]
  calc
    _ <= n ^ (totalWeight K - 1) * ⨆ i, v (![(x : K), n] i) := by
      gcongr; exact Finite.le_ciSup_of_le 0 le_rfl
    _ <= (∏ v' in univ.erase v, (⨆ i, v' (![↑x, ↑n] i)) ^ v'.mult) *
         (⨆ i, v (![↑x, ↑n] i)) ^ (v.mult - 1) * ⨆ i, v 
-/
private lemma infinitePlace_apply_le_of_prod_le {n : Nat} (hn : n != 0) (B : Real) {x : 𝓞 K}
    (h : ∏ v : InfinitePlace K, (⨆ i, v (![(x : K), n] i)) ^ v.mult <= B) (v : InfinitePlace K) :
    v x <= B / n ^ (totalWeight K - 1) := by
  classical
  rw [le_div_iff₀' (by positivity)]
  calc
    _ <= n ^ (totalWeight K - 1) * ⨆ i, v (![(x : K), n] i) := by
      gcongr; exact Finite.le_ciSup_of_le 0 le_rfl
    _ <= (∏ v' in univ.erase v, (⨆ i, v' (![↑x, ↑n] i)) ^ v'.mult) *
         (⨆ i, v (![↑x, ↑n] i)) ^ (v.mult - 1) * ⨆ i, v (![(x : K), n] i) := by
      rw [pow_totalWeight_sub_one_eq hn]
      gcongr
      · exact Real.iSup_nonneg_of_nonnegHomClass ..
      · exact prod_nonneg fun _ _ => pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass ..) _
all_goals exact Finite.le_ciSup_of_le 1 by simp
    _ <= B := by
      rwa [mul_assoc, pow_sub_one_mul v.mult_ne_zero, prod_erase_mul _ _ (mem_univ v)]

end withFinset

/--
lemma `finite_setOfPred_prod_infinitePlace_iSup_le` / 引理 `finite_setOfPred_prod_infinitePlace_iSup_le`

English:
lemma finite_setOfPred_prod_infinitePlace_iSup_le
  given: {n : Nat} (hn : n != 0) (B : Real)
  proof: by
  set B' := B / n ^ (totalWeight K - 1)
  suffices Set.BijOn ((↑) : 𝓞 K -> K) {x | forall (v : InfinitePlace K), v x <= B'}
      {x | IsIntegral Int x ∧ forall (φ : K ->+* Complex), ‖φ x‖ <= B'} from
.subset this.finite_iff_finite.mpr (Embeddings.finite_of_norm_le K Complex B')
      fun _ _ => 

中文:
引理 finite_setOfPred_prod_infinitePlace_iSup_le
  条件: {n : 自然数} (hn : n != 0) (B : 实数)
  证明: by
  set B' := B / n ^ (totalWeight K - 1)
  suffices Set.BijOn ((↑) : 𝓞 K -> K) {x | forall (v : InfinitePlace K), v x <= B'}
      {x | IsIntegral Int x ∧ forall (φ : K ->+* Complex), ‖φ x‖ <= B'} from
.subset this.finite_iff_finite.mpr (Embeddings.finite_of_norm_le K Complex B')
      fun _ _ => 

Depends on / 依赖: Embeddings, Embeddings.finite_of_norm_le, InfinitePlace, IsIntegral, RingOfIntegers, RingOfIntegers.ext, Set.BijOn, Set.mem_image, Set.mem_ofPred_eq, finite_iff_finite, finite_of_norm_le, infinitePlace_apply_le_of_prod_le, isIntegral_coe, mem_image, mem_ofPred_eq, subset, this.finite_iff_finite.mpr, totalWeight, x.isIntegral_coe
-/
lemma finite_setOfPred_prod_infinitePlace_iSup_le {n : Nat} (hn : n != 0) (B : Real) :
    {x : 𝓞 K | ∏ v : InfinitePlace K, (⨆ i, v (![(x : K), n] i)) ^ v.mult <= B}.Finite := by
  set B' := B / n ^ (totalWeight K - 1)
  suffices Set.BijOn ((↑) : 𝓞 K -> K) {x | forall (v : InfinitePlace K), v x <= B'}
      {x | IsIntegral Int x ∧ forall (φ : K ->+* Complex), ‖φ x‖ <= B'} from
.subset this.finite_iff_finite.mpr (Embeddings.finite_of_norm_le K Complex B')
      fun _ _ => by grind [infinitePlace_apply_le_of_prod_le hn B]
  refine .mk (fun x hx => ?_) (fun _ _ _ _ => RingOfIntegers.ext) fun a ha => ?_ <;>
    simp only [Set.mem_image, Set.mem_ofPred_eq] at *
· exact ⟨x.isIntegral_coe, fun φ => hx .mk φ⟩
  · rw [← mem_integralClosure_iff Int K] at ha
    exact ⟨⟨a, ha.1⟩, fun v => v.norm_embedding_eq a ▸ ha.2 v.embedding, rfl⟩

@[deprecated (since := "2026-07-09")]
alias finite_setOf_prod_infinitePlace_iSup_le := finite_setOfPred_prod_infinitePlace_iSup_le

/--
lemma `finite_setOfPred_mulHeight_nat_le` / 引理 `finite_setOfPred_mulHeight_nat_le`

English:
lemma finite_setOfPred_mulHeight_nat_le
  given: {n : Nat} (hn : n != 0) (B : Real)
  proof: by
  suffices {a : 𝓞 K | mulHeight ![(a : K), n] <= B} subseteq
      {a | ∏ v : InfinitePlace K, (⨆ i, v (![(a : K), n] i)) ^ v.mult <= n ^ totalWeight K * B} from
    (finite_setOfPred_prod_infinitePlace_iSup_le hn _).subset this
  refine Set.ofPred_subset_ofPred_of_imp fun a ha => ?_
  rw [mulHei

中文:
引理 finite_setOfPred_mulHeight_nat_le
  条件: {n : 自然数} (hn : n != 0) (B : 实数)
  证明: by
  suffices {a : 𝓞 K | mulHeight ![(a : K), n] <= B} subseteq
      {a | ∏ v : InfinitePlace K, (⨆ i, v (![(a : K), n] i)) ^ v.mult <= n ^ totalWeight K * B} from
    (finite_setOfPred_prod_infinitePlace_iSup_le hn _).subset this
  refine Set.ofPred_subset_ofPred_of_imp fun a ha => ?_
  rw [mulHei

Depends on / 依赖: InfinitePlace, Set.ofPred_subset_ofPred_of_imp, finite_setOfPred_prod_infinitePlace_iSup_le, mulHeight, mulHeight_eq, mul_assoc, mul_comm, ofPred_subset_ofPred_of_imp, one_le_pow_totalWeight_mul_finprod, one_mul, subset, subseteq, totalWeight, v.mult
-/
lemma finite_setOfPred_mulHeight_nat_le {n : Nat} (hn : n != 0) (B : Real) :
    {a : 𝓞 K | mulHeight ![(a : K), n] <= B}.Finite := by
  suffices {a : 𝓞 K | mulHeight ![(a : K), n] <= B} subseteq
      {a | ∏ v : InfinitePlace K, (⨆ i, v (![(a : K), n] i)) ^ v.mult <= n ^ totalWeight K * B} from
    (finite_setOfPred_prod_infinitePlace_iSup_le hn _).subset this
  refine Set.ofPred_subset_ofPred_of_imp fun a ha => ?_
  rw [mulHeight_eq <| by simp [hn], mul_comm] at ha
  grw [← ha, ← mul_assoc, ← one_le_pow_totalWeight_mul_finprod hn, one_mul]
  -- nonnegativity side goal
  exact Finset.prod_nonneg fun _ _ => pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass ..) _

@[deprecated (since := "2026-07-09")]
alias finite_setOf_mulHeight_nat_le := finite_setOfPred_mulHeight_nat_le

variable (K) in
/--
lemma `finite_setOfPred_isIntegral_nat_mul_and_mulHeight₁_le` / 引理 `finite_setOfPred_isIntegral_nat_mul_and_mulHeight₁_le`

English:
lemma finite_setOfPred_isIntegral_nat_mul_and_mulHeight₁_le
  given: {n : Nat} (hn : n != 0) (B : Real)
  proof: by
  have hn' : (n : K) != 0 := mod_cast hn
  suffices Set.BijOn (fun a : 𝓞 K => (a / n : K)) {a | mulHeight ![(a : K), n] <= B}
      {x | IsIntegral Int (n * x) ∧ mulHeight₁ x <= B} from
this.finite_iff_finite.mp finite_setOfPred_mulHeight_nat_le hn B
  refine .mk (fun a ha => ?_) (fun a _ b _ h =

中文:
引理 finite_setOfPred_isIntegral_nat_mul_and_mulHeight₁_le
  条件: {n : 自然数} (hn : n != 0) (B : 实数)
  证明: by
  have hn' : (n : K) != 0 := mod_cast hn
  suffices Set.BijOn (fun a : 𝓞 K => (a / n : K)) {a | mulHeight ![(a : K), n] <= B}
      {x | IsIntegral Int (n * x) ∧ mulHeight₁ x <= B} from
this.finite_iff_finite.mp finite_setOfPred_mulHeight_nat_le hn B
  refine .mk (fun a ha => ?_) (fun a _ b _ h =
-/
private lemma finite_setOfPred_isIntegral_nat_mul_and_mulHeight₁_le {n : Nat} (hn : n != 0) (B : Real) :
    {x : K | IsIntegral Int (n * x) ∧ mulHeight₁ x <= B}.Finite := by
  have hn' : (n : K) != 0 := mod_cast hn
  suffices Set.BijOn (fun a : 𝓞 K => (a / n : K)) {a | mulHeight ![(a : K), n] <= B}
      {x | IsIntegral Int (n * x) ∧ mulHeight₁ x <= B} from
this.finite_iff_finite.mp finite_setOfPred_mulHeight_nat_le hn B
  refine .mk (fun a ha => ?_) (fun a _ b _ h => ?_) fun x ⟨hx₁, hx₂⟩ => ?_
  · simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [mul_div_cancel₀ (a : K) hn']; rw [mulHeight₁_div_eq_mulHeight]
    exact ⟨a.isIntegral_coe, ha⟩
  · rwa [div_left_inj' hn', RingOfIntegers.eq_iff] at h
  · simp only [Set.mem_ofPred_eq, Set.mem_image]
    obtain ⟨a, ha⟩ : exists a : 𝓞 K, n * x = a := ⟨⟨_, hx₁⟩, rfl⟩
    refine ⟨a, ?_, (EuclideanDomain.eq_div_of_mul_eq_right hn' ha).symm⟩
    rwa [← ha, ← mulHeight₁_div_eq_mulHeight, mul_div_cancel_left₀ x hn']

variable (K) in
/--
theorem `finite_setOfPred_mulHeight₁_le` / 定理 `finite_setOfPred_mulHeight₁_le`

English:
theorem finite_setOfPred_mulHeight₁_le
  given: (B : Real)
  statement: {x : K | mulHeight₁ x <= B}.Finite
  proof: by
  have H : {x : K | mulHeight₁ x <= B} =
      ⋃ n : Fin ⌊B⌋₊, {x : K | IsIntegral Int ((n + 1) * x) ∧ mulHeight₁ x <= B} := by
    ext x : 1
    obtain ⟨n, hn₀, hn₁, hn⟩ := exists_nat_le_mulHeight₁ x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_and_right, iff_and_self]
    refine fun

中文:
定理 finite_setOfPred_mulHeight₁_le
  条件: (B : 实数)
  结论: {x : K | mulHeight₁ x <= B}.Finite
  证明: by
  have H : {x : K | mulHeight₁ x <= B} =
      ⋃ n : Fin ⌊B⌋₊, {x : K | IsIntegral Int ((n + 1) * x) ∧ mulHeight₁ x <= B} := by
    ext x : 1
    obtain ⟨n, hn₀, hn₁, hn⟩ := exists_nat_le_mulHeight₁ x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_and_right, iff_and_self]
    refine fun

Depends on / 依赖: IsIntegral, Nat.cast_add_one, Nat.le_floor, Nat.sub_one_add_one, Nat.zero, Set.finite_iUnion, Set.mem_iUnion, Set.mem_ofPred_eq, cast_add_one, exists_and_right, finite_iUnion, iff_and_self, le_floor, mem_iUnion, mem_ofPred_eq, mod_cast, sub_one_add_one
-/
theorem finite_setOfPred_mulHeight₁_le (B : Real) : {x : K | mulHeight₁ x <= B}.Finite := by
  have H : {x : K | mulHeight₁ x <= B} =
      ⋃ n : Fin ⌊B⌋₊, {x : K | IsIntegral Int ((n + 1) * x) ∧ mulHeight₁ x <= B} := by
    ext x : 1
    obtain ⟨n, hn₀, hn₁, hn⟩ := exists_nat_le_mulHeight₁ x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_and_right, iff_and_self]
    refine fun h => ⟨⟨n - 1, by grind [Nat.le_floor <| hn₁.trans h]⟩, ?_⟩
    rwa [← Nat.cast_add_one, Nat.sub_one_add_one hn₀]
  rw [H]
  exact Set.finite_iUnion fun n =>
    mod_cast finite_setOfPred_isIntegral_nat_mul_and_mulHeight₁_le K (Nat.zero_ne_add_one n).symm B

@[deprecated (since := "2026-07-09")]
alias finite_setOf_mulHeight₁_le := finite_setOfPred_mulHeight₁_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Northcott (mulHeight₁ (K := K))
  body: finite_setOfPred_mulHeight₁_le K

中文:
实例 :
  签名: Northcott (mulHeight₁ (K := K))
  定义体: finite_setOfPred_mulHeight₁_le K
-/
instance : Northcott (mulHeight₁ (K := K)) where
  finite_le := finite_setOfPred_mulHeight₁_le K

variable (K) in
/--
theorem `finite_setOfPred_logHeight₁_le` / 定理 `finite_setOfPred_logHeight₁_le`

English:
theorem finite_setOfPred_logHeight₁_le
  given: (B : Real)
  proof: Northcott.finite_le B

@[deprecated (since := "2026-07-09")]
alias finite_setOf_logHeight₁_le := finite_setOfPred_logHeight₁_le

中文:
定理 finite_setOfPred_logHeight₁_le
  条件: (B : 实数)
  证明: Northcott.finite_le B

@[deprecated (since := "2026-07-09")]
alias finite_setOf_logHeight₁_le := finite_setOfPred_logHeight₁_le

Depends on / 依赖: Northcott, Northcott.finite_le, finite_le
-/
theorem finite_setOfPred_logHeight₁_le (B : Real) :
    {x : K | logHeight₁ x <= B}.Finite :=
  Northcott.finite_le B

@[deprecated (since := "2026-07-09")]
alias finite_setOf_logHeight₁_le := finite_setOfPred_logHeight₁_le

end NumberField

end Northcott

/-!
### Positivity extension for totalWeight on number fields
-/

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `Height.totalWeight` is positive for number fields. -/
@[positivity Height.totalWeight _]
meta def evalHeightTotalWeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Nat), ~q(@Height.totalWeight $K $KF $KA) =>
    -- Check whether there is a `NumberField` instance for `$K` around.
    match ← trySynthInstanceQ q(NumberField $K) with
    | .some _inst =>
      assertInstancesCommute
      return .positive q(NumberField.totalWeight_pos $K)
    | _ => throwError "field in Height.totalWeight not known to be a number field"
  | _, _, _ => throwError "not Height.totalWeight"

end Mathlib.Meta.Positivity

/-!
### Heights over the rational numbers

We show that the `Height.mulHeight` of a tuple of coprime integers (considered as rational numbers)
equals the maximum of their absolute values and that the `Height.mulHeight₁` of a rational
number is the maximum of the absolute value of the numerator and the denominator.
We add the corresponding results for logarithmic heights.
-/

namespace Rat

open NumberField Height

section tuples

variable {ι : Type*} [Fintype ι] [Nonempty ι] {x : ι -> Int}

/--
lemma `iSup_finitePlace_apply_eq_one_of_gcd_eq_one` / 引理 `iSup_finitePlace_apply_eq_one_of_gcd_eq_one`

English:
lemma iSup_finitePlace_apply_eq_one_of_gcd_eq_one
  given: (v : FinitePlace Rat) (hx : Finset.univ.gcd x = 1)
  proof: by
  have hv : IsNonarchimedean (v ·) := FinitePlace.add_le v
  have H (n : Int) : v n <= 1 := IsNonarchimedean.apply_intCast_le_one hv
  obtain ⟨f, hf⟩ := Finset.gcd_eq_sum_mul .univ x
  apply_fun v at hf
  simp_rw [hx, Int.cast_one, map_one, Int.cast_sum, Int.cast_mul] at hf
  replace hf := hf.tra

中文:
引理 iSup_finitePlace_apply_eq_one_of_gcd_eq_one
  条件: (v : FinitePlace Rat) (hx : Finset.univ.gcd x = 1)
  证明: by
  have hv : IsNonarchimedean (v ·) := FinitePlace.add_le v
  have H (n : Int) : v n <= 1 := IsNonarchimedean.apply_intCast_le_one hv
  obtain ⟨f, hf⟩ := Finset.gcd_eq_sum_mul .univ x
  apply_fun v at hf
  simp_rw [hx, Int.cast_one, map_one, Int.cast_sum, Int.cast_mul] at hf
  replace hf := hf.tra

Depends on / 依赖: FinitePlace, FinitePlace.add_le, Finset, Finset.gcd_eq_sum_mul, Int.cast_mul, Int.cast_one, Int.cast_sum, IsNonarchimedean, IsNonarchimedean.apply_intCast_le_one, add_le, apply_fun, apply_intCast_le_one, apply_nonneg, apply_sum_univ_le, cast_mul, cast_one, cast_sum, exists_eq_ciSup_of_finite, gcd_eq_sum_mul, hf.trans
-/
lemma iSup_finitePlace_apply_eq_one_of_gcd_eq_one (v : FinitePlace Rat) (hx : Finset.univ.gcd x = 1) :
    ⨆ i, v (x i) = 1 := by
  have hv : IsNonarchimedean (v ·) := FinitePlace.add_le v
  have H (n : Int) : v n <= 1 := IsNonarchimedean.apply_intCast_le_one hv
  obtain ⟨f, hf⟩ := Finset.gcd_eq_sum_mul .univ x
  apply_fun v at hf
  simp_rw [hx, Int.cast_one, map_one, Int.cast_sum, Int.cast_mul] at hf
  replace hf := hf.trans_le hv.apply_sum_univ_le
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => v (x i * f i))
  rw [← hi]; rw [map_mul] at hf
replace hf : 1 <= v (x i) := hf.trans mul_le_of_le_one_right (apply_nonneg v _) (H _)
exact le_antisymm (ciSup_le (H <| x ·)) Finite.le_ciSup_of_le i hf

open AdmissibleAbsValues in
/--
lemma `mulHeight_eq_max_abs_of_gcd_eq_one` / 引理 `mulHeight_eq_max_abs_of_gcd_eq_one`

English:
lemma mulHeight_eq_max_abs_of_gcd_eq_one
  given: (hx : Finset.univ.gcd x = 1)
  proof: by
  have hx₀ : Int.cast ∘ x != (0 : ι -> Rat) := by
    contrapose! hx
    rw [Function.comp_eq_zero_iff x intCast_injective Rat.intCast_zero] at hx
    rw [hx]; rw [Finset.gcd_eq_zero_iff.mpr (by simp)]
    exact zero_ne_one
  simp_rw [Finite.map_iSup_of_monotone _ Int.cast_mono, NumberField.mulHe

中文:
引理 mulHeight_eq_max_abs_of_gcd_eq_one
  条件: (hx : Finset.univ.gcd x = 1)
  证明: by
  have hx₀ : Int.cast ∘ x != (0 : ι -> Rat) := by
    contrapose! hx
    rw [Function.comp_eq_zero_iff x intCast_injective Rat.intCast_zero] at hx
    rw [hx]; rw [Finset.gcd_eq_zero_iff.mpr (by simp)]
    exact zero_ne_one
  simp_rw [Finite.map_iSup_of_monotone _ Int.cast_mono, NumberField.mulHe

Depends on / 依赖: Finite, Finite.map_iSup_of_monotone, Finset, Finset.gcd_eq_zero_iff.mpr, Function, Function.comp_eq_zero_iff, Int.cast, Int.cast_mono, NumberField, NumberField.mulHeight_eq, Rat.intCast_zero, cast_mono, comp_eq_zero_iff, contrapose, finprod_eq_one_of_forall_eq_one, gcd_eq_zero_iff, iSup_finitePlace_apply_eq_one_of_gcd_eq_one, infinitePlace_apply, intCast_injective, intCast_zero
-/
lemma mulHeight_eq_max_abs_of_gcd_eq_one (hx : Finset.univ.gcd x = 1) :
    mulHeight (((↑) : Int -> Rat) ∘ x) = ⨆ i, |x i| := by
  have hx₀ : Int.cast ∘ x != (0 : ι -> Rat) := by
    contrapose! hx
    rw [Function.comp_eq_zero_iff x intCast_injective Rat.intCast_zero] at hx
    rw [hx]; rw [Finset.gcd_eq_zero_iff.mpr (by simp)]
    exact zero_ne_one
  simp_rw [Finite.map_iSup_of_monotone _ Int.cast_mono, NumberField.mulHeight_eq hx₀,
    infinitePlace_apply]
  simp [finprod_eq_one_of_forall_eq_one (iSup_finitePlace_apply_eq_one_of_gcd_eq_one · hx)]

open Real in
/--
lemma `logHeight_eq_max_abs_of_gcd_eq_one` / 引理 `logHeight_eq_max_abs_of_gcd_eq_one`

English:
lemma logHeight_eq_max_abs_of_gcd_eq_one
  given: (hx : Finset.univ.gcd x = 1)
  proof: by
  rw [logHeight_eq_log_mulHeight]; rw [mulHeight_eq_max_abs_of_gcd_eq_one hx]

中文:
引理 logHeight_eq_max_abs_of_gcd_eq_one
  条件: (hx : Finset.univ.gcd x = 1)
  证明: by
  rw [logHeight_eq_log_mulHeight]; rw [mulHeight_eq_max_abs_of_gcd_eq_one hx]

Depends on / 依赖: logHeight_eq_log_mulHeight, mulHeight_eq_max_abs_of_gcd_eq_one
-/
lemma logHeight_eq_max_abs_of_gcd_eq_one (hx : Finset.univ.gcd x = 1) :
    logHeight (((↑) : Int -> Rat) ∘ x) = log ↑(⨆ i, |x i|) := by
  rw [logHeight_eq_log_mulHeight]; rw [mulHeight_eq_max_abs_of_gcd_eq_one hx]

end tuples

section mulHeight₁

/--
lemma `mulHeight_self_one_eq_mulHeight_num_den` / 引理 `mulHeight_self_one_eq_mulHeight_num_den`

English:
lemma mulHeight_self_one_eq_mulHeight_num_den
  given: (q : Rat)
  proof: by
  have hq₀ : (q.den : Rat) != 0 := mod_cast q.den_nz
  rw [← mulHeight_smul_eq_mulHeight _ hq₀]
  simp

中文:
引理 mulHeight_self_one_eq_mulHeight_num_den
  条件: (q : Rat)
  证明: by
  have hq₀ : (q.den : Rat) != 0 := mod_cast q.den_nz
  rw [← mulHeight_smul_eq_mulHeight _ hq₀]
  simp

Depends on / 依赖: den_nz, mod_cast, mulHeight_smul_eq_mulHeight, q.den, q.den_nz
-/
lemma mulHeight_self_one_eq_mulHeight_num_den (q : Rat) :
    mulHeight ![q, 1] = mulHeight ![(q.num : Rat), q.den] := by
  have hq₀ : (q.den : Rat) != 0 := mod_cast q.den_nz
  rw [← mulHeight_smul_eq_mulHeight _ hq₀]
  simp

/--
lemma `mulHeight₁_eq_max` / 引理 `mulHeight₁_eq_max`

English:
lemma mulHeight₁_eq_max
  given: (q : Rat)
  statement: mulHeight₁ q = max q.num.natAbs q.den
  proof: by
  rw [mulHeight₁_eq_mulHeight]; rw [mulHeight_self_one_eq_mulHeight_num_den]; rw [← intCast_natCast q.den]
  have : (.univ : Finset (Fin 2)).gcd ![q.num, q.den] = 1 := by
    simpa [Finset.univ_fin2, Int.normalize_coe_nat, ← Int.coe_gcd q.num q.den] using
Int.isCoprime_iff_gcd_eq_one.mp isCoprime

中文:
引理 mulHeight₁_eq_max
  条件: (q : Rat)
  结论: mulHeight₁ q = max q.num.natAbs q.den
  证明: by
  rw [mulHeight₁_eq_mulHeight]; rw [mulHeight_self_one_eq_mulHeight_num_den]; rw [← intCast_natCast q.den]
  have : (.univ : Finset (Fin 2)).gcd ![q.num, q.den] = 1 := by
    simpa [Finset.univ_fin2, Int.normalize_coe_nat, ← Int.coe_gcd q.num q.den] using
Int.isCoprime_iff_gcd_eq_one.mp isCoprime

Depends on / 依赖: Finset, Finset.univ_fin2, Int.cast_inj, Int.cast_natCast, Int.coe_gcd, Int.isCoprime_iff_gcd_eq_one.mp, Int.normalize_coe_nat, cast_inj, cast_natCast, ciSup_le, coe_gcd, convert, fin_cases, intCast_natCast, isCoprime_iff_gcd_eq_one, isCoprime_num_den, le_antisymm, max_le, mulHeight_eq_max_abs_of_gcd_eq_one, mulHeight_self_one_eq_mulHeight_num_den
-/
lemma mulHeight₁_eq_max (q : Rat) : mulHeight₁ q = max q.num.natAbs q.den := by
  rw [mulHeight₁_eq_mulHeight]; rw [mulHeight_self_one_eq_mulHeight_num_den]; rw [← intCast_natCast q.den]
  have : (.univ : Finset (Fin 2)).gcd ![q.num, q.den] = 1 := by
    simpa [Finset.univ_fin2, Int.normalize_coe_nat, ← Int.coe_gcd q.num q.den] using
Int.isCoprime_iff_gcd_eq_one.mp isCoprime_num_den q
  convert! mulHeight_eq_max_abs_of_gcd_eq_one this
  · ext i; fin_cases i <;> simp
  · rw [← Int.cast_natCast, Int.cast_inj]
    push_cast
refine le_antisymm (max_le ?_ ?_) ciSup_le fun i => ?_
· exact Finite.le_ciSup_of_le 0 by simp
· exact Finite.le_ciSup_of_le 1 by simp
    · fin_cases i <;> simp

open Real in
/--
lemma `logHeight₁_eq_log_max` / 引理 `logHeight₁_eq_log_max`

English:
lemma logHeight₁_eq_log_max
  given: (q : Rat)
  statement: logHeight₁ q = log ↑(max q.num.natAbs q.den)
  proof: by
  rw [logHeight₁_eq_log_mulHeight₁]; rw [mulHeight₁_eq_max]

中文:
引理 logHeight₁_eq_log_max
  条件: (q : Rat)
  结论: logHeight₁ q = log ↑(max q.num.natAbs q.den)
  证明: by
  rw [logHeight₁_eq_log_mulHeight₁]; rw [mulHeight₁_eq_max]
-/
lemma logHeight₁_eq_log_max (q : Rat) : logHeight₁ q = log ↑(max q.num.natAbs q.den) := by
  rw [logHeight₁_eq_log_mulHeight₁]; rw [mulHeight₁_eq_max]

/--
theorem `mulHeight₁_natCast` / 定理 `mulHeight₁_natCast`

English:
theorem mulHeight₁_natCast
  given: (n : Nat) [NeZero n]
  proof: by
  simp [mulHeight₁_eq_max, show 1 <= n by grind [NeZero.ne n]]

中文:
定理 mulHeight₁_natCast
  条件: (n : 自然数) [NeZero n]
  证明: by
  simp [mulHeight₁_eq_max, show 1 <= n by grind [NeZero.ne n]]

Depends on / 依赖: NeZero, NeZero.ne
-/
theorem mulHeight₁_natCast (n : Nat) [NeZero n] :
    mulHeight₁ (n : Rat) = n := by
  simp [mulHeight₁_eq_max, show 1 <= n by grind [NeZero.ne n]]

/--
theorem `logHeight₁_natCast` / 定理 `logHeight₁_natCast`

English:
theorem logHeight₁_natCast
  given: (n : Nat) [NeZero n]
  proof: by
  simp [logHeight₁_eq_log_mulHeight₁, mulHeight₁_natCast n]

中文:
定理 logHeight₁_natCast
  条件: (n : 自然数) [NeZero n]
  证明: by
  simp [logHeight₁_eq_log_mulHeight₁, mulHeight₁_natCast n]
-/
theorem logHeight₁_natCast (n : Nat) [NeZero n] :
    logHeight₁ (n : Rat) = Real.log n := by
  simp [logHeight₁_eq_log_mulHeight₁, mulHeight₁_natCast n]

end mulHeight₁

end Rat

end
