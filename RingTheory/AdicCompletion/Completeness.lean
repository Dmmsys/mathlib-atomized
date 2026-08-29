/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Basic

import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# Completeness of the Adic Completion for Finitely Generated Ideals

This file establishes that `AdicCompletion I M` is itself `I`-adically complete
when the ideal `I` is finitely generated.

## Main definitions

* `AdicCompletion.ofPowSMul`: The canonical inclusion between adic completions
  induced by the inclusion from `I ^ n • M` to `M`.

* `AdicCompletion.ofValEqZero`: Given `x` in `AdicCompletion I M` projecting to zero
  in `M / I ^ n • M`, `ofValEqZero` constructs the corresponding element in
  the adic completion of `I ^ n • M`.

## Main results

* `AdicCompletion.pow_smul_top_eq_ker_eval`: `I ^ n • AdicCompletion I M` is exactly the kernel
  of the evaluation map `eval I M n` when `I` is finitely generated.

* `AdicCompletion.isAdicComplete`: `AdicCompletion I M` is `I`-adically complete if `I` is
  finitely generated.

* `MvPowerSeries.isAdicComplete`: Multivariate power series is adic complete with respect to
  the ideal spanned by all variables when the index is finite.

-/

public section

noncomputable section

open Submodule Finsupp

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {a b c : Nat}

namespace AdicCompletion

variable (M) in
/--
Definition of `ofPowSMul` / `ofPowSMul` 的定义

English:
abbreviation ofPowSMul
  signature: (n : Nat)
  body: map I (I ^ n • ⊤ : Submodule R M).subtype

中文:
缩写 ofPowSMul
  签名: (n : 自然数)
  定义体: map I (I ^ n • ⊤ : Submodule R M).subtype

Depends on / 依赖: Submodule, subtype
-/
abbrev ofPowSMul (n : Nat) : AdicCompletion I ↥(I ^ n • ⊤ : Submodule R M)
    ->ₗ[AdicCompletion I R] AdicCompletion I M := map I (I ^ n • ⊤ : Submodule R M).subtype

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ofPowSMul_val_apply` / 定理 `ofPowSMul_val_apply`

English:
theorem ofPowSMul_val_apply
  given: (h : c = b + a) {x : AdicCompletion I ↥(I ^ a • ⊤ : Submodule R M)}
  proof: by
  rw [← x.prop (show b <= c by lia)]; rw [map_val_apply]
  refine Quotient.induction_on _ (x.val c) fun z => ?_
  simp [powSMulQuotInclusion]

中文:
定理 ofPowSMul_val_apply
  条件: (h : c = b + a) {x : AdicCompletion I ↥(I ^ a • ⊤ : 子模 R M)}
  证明: by
  rw [← x.prop (show b <= c by lia)]; rw [map_val_apply]
  refine Quotient.induction_on _ (x.val c) fun z => ?_
  simp [powSMulQuotInclusion]

Depends on / 依赖: Quotient, Quotient.induction_on, induction_on, map_val_apply, powSMulQuotInclusion, x.prop, x.val
-/
theorem ofPowSMul_val_apply (h : c = b + a) {x : AdicCompletion I ↥(I ^ a • ⊤ : Submodule R M)} :
    (ofPowSMul I M a x).val c = powSMulQuotInclusion I M h ⊤ (x.val b) := by
  rw [← x.prop (show b <= c by lia)]; rw [map_val_apply]
  refine Quotient.induction_on _ (x.val c) fun z => ?_
  simp [powSMulQuotInclusion]

/--
theorem `ofPowSMul_val_apply_eq_zero` / 定理 `ofPowSMul_val_apply_eq_zero`

English:
theorem ofPowSMul_val_apply_eq_zero
  statement: (h : a <= b)
  proof: by
  rw [map_val_apply]
  refine Quotient.induction_on _ (x.val a) fun z => ?_
  simpa using pow_smul_top_le _ _ h z.prop

中文:
定理 ofPowSMul_val_apply_eq_zero
  结论: (h : a <= b)
  证明: by
  rw [map_val_apply]
  refine Quotient.induction_on _ (x.val a) fun z => ?_
  simpa using pow_smul_top_le _ _ h z.prop

Depends on / 依赖: Quotient, Quotient.induction_on, induction_on, map_val_apply, pow_smul_top_le, x.val, z.prop
-/
theorem ofPowSMul_val_apply_eq_zero (h : a <= b)
    {x : AdicCompletion I ↥(I ^ b • ⊤ : Submodule R M)} : (ofPowSMul I M b x).val a = 0 := by
  rw [map_val_apply]
  refine Quotient.induction_on _ (x.val a) fun z => ?_
  simpa using pow_smul_top_le _ _ h z.prop

/--
theorem `ofPowSMul_injective` / 定理 `ofPowSMul_injective`

English:
theorem ofPowSMul_injective
  given: (n : Nat)
  statement: Function.Injective (ofPowSMul I M n)
  proof: by
  rw [← LinearMap.ker_eq_bot]; rw [LinearMap.ker_eq_bot']
  intro x hx; ext i
  simp only [AdicCompletion.ext_iff, val_zero, Pi.zero_apply] at hx
  specialize hx (i + n)
  rw [ofPowSMul_val_apply I (by rw [add_comm]),
    LinearMap.map_eq_zero_iff _ (powSMulQuotInclusion_injective ..)] at hx
  simp [hx]

中文:
定理 ofPowSMul_injective
  条件: (n : 自然数)
  结论: 函数.单射 (ofPowSMul I M n)
  证明: by
  rw [← LinearMap.ker_eq_bot]; rw [LinearMap.ker_eq_bot']
  intro x hx; ext i
  simp only [AdicCompletion.ext_iff, val_zero, Pi.zero_apply] at hx
  specialize hx (i + n)
  rw [ofPowSMul_val_apply I (by rw [add_comm]),
    LinearMap.map_eq_zero_iff _ (powSMulQuotInclusion_injective ..)] at hx
  simp [hx]

Depends on / 依赖: AdicCompletion, AdicCompletion.ext_iff, LinearMap, LinearMap.ker_eq_bot, LinearMap.map_eq_zero_iff, Pi.zero_apply, add_comm, ext_iff, ker_eq_bot, map_eq_zero_iff, ofPowSMul_val_apply, powSMulQuotInclusion_injective, specialize, val_zero, zero_apply
-/
theorem ofPowSMul_injective (n : Nat) : Function.Injective (ofPowSMul I M n) := by
  rw [← LinearMap.ker_eq_bot]; rw [LinearMap.ker_eq_bot']
  intro x hx; ext i
  simp only [AdicCompletion.ext_iff, val_zero, Pi.zero_apply] at hx
  specialize hx (i + n)
  rw [ofPowSMul_val_apply I (by rw [add_comm]),
    LinearMap.map_eq_zero_iff _ (powSMulQuotInclusion_injective ..)] at hx
  simp [hx]

/--
lemma `ofValEqZeroAux_exists` / 引理 `ofValEqZeroAux_exists`

English:
lemma ofValEqZeroAux_exists
  statement: {x : AdicCompletion I M} (h : c = b + a)
  proof: by
  simpa [← LinearMap.mem_range, range_powSMulQuotInclusion] using
    (val_apply_mem_smul_top_iff I (show a <= c by lia)).mpr ha

中文:
引理 ofValEqZeroAux_存在
  结论: {x : AdicCompletion I M} (h : c = b + a)
  证明: by
  simpa [← LinearMap.mem_range, range_powSMulQuotInclusion] using
    (val_apply_mem_smul_top_iff I (show a <= c by lia)).mpr ha
-/
private lemma ofValEqZeroAux_exists {x : AdicCompletion I M} (h : c = b + a)
    (ha : x.val a = 0) : exists t, powSMulQuotInclusion I M h ⊤ t = x.val c := by
  simpa [← LinearMap.mem_range, range_powSMulQuotInclusion] using
    (val_apply_mem_smul_top_iff I (show a <= c by lia)).mpr ha

/--
Definition of `ofValEqZeroAux` / `ofValEqZeroAux` 的定义

English:
definition ofValEqZeroAux
  signature: {x : AdicCompletion I M} (h : c = b + a) (ha : x.val a = 0)
  body: Exists.choose (ofValEqZeroAux_exists I h ha)

中文:
定义 ofValEqZeroAux
  签名: {x : AdicCompletion I M} (h : c = b + a) (ha : x.val a = 0)
  定义体: Exists.choose (ofValEqZeroAux_exists I h ha)

Depends on / 依赖: Exists, Exists.choose, ofValEqZeroAux_exists
-/
def ofValEqZeroAux {x : AdicCompletion I M} (h : c = b + a) (ha : x.val a = 0) :
    ↥(I ^ a • ⊤ : Submodule R M) ⧸ I ^ b • (⊤ : Submodule R ↥(I ^ a • ⊤ : Submodule R M)) :=
  Exists.choose (ofValEqZeroAux_exists I h ha)

/--
lemma `ofValEqZeroAux_prop` / 引理 `ofValEqZeroAux_prop`

English:
lemma ofValEqZeroAux_prop
  statement: {x : AdicCompletion I M} (h : c = b + a)
  proof: Exists.choose_spec (ofValEqZeroAux_exists I h ha)

中文:
引理 ofValEqZeroAux_prop
  结论: {x : AdicCompletion I M} (h : c = b + a)
  证明: Exists.choose_spec (ofValEqZeroAux_exists I h ha)
-/
private lemma ofValEqZeroAux_prop {x : AdicCompletion I M} (h : c = b + a)
    (ha : x.val a = 0) : (powSMulQuotInclusion I M h ⊤) (ofValEqZeroAux I h ha) = x.val c :=
  Exists.choose_spec (ofValEqZeroAux_exists I h ha)

/--
Definition of `ofValEqZero` / `ofValEqZero` 的定义

English:
definition ofValEqZero
  signature: {n : Nat} {x : AdicCompletion I M} (hxn : x.val n = 0)
  body: ofValEqZeroAux I (Eq.refl (i + n)) hxn
  property {i j} h := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← (powSMulQuotInclusion_injective I rfl ⊤).eq_iff]; rw [ofValEqZeroAux_prop]; rw [← LinearMap.comp_apply]; rw [← factorPow_comp_powSMulQuotInclusion I rfl
      (show i + k + n = k + (i + n) by ring)]; rw [LinearMap.comp_apply]; rw [ofValEqZeroAux_prop]
    exact x.prop (by lia)

@[simp]

中文:
定义 ofValEqZero
  签名: {n : 自然数} {x : AdicCompletion I M} (hxn : x.val n = 0)
  定义体: ofValEqZeroAux I (Eq.refl (i + n)) hxn
  property {i j} h := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← (powSMulQuotInclusion_injective I rfl ⊤).eq_iff]; rw [ofValEqZeroAux_prop]; rw [← LinearMap.comp_apply]; rw [← factorPow_comp_powSMulQuotInclusion I rfl
      (show i + k + n = k + (i + n) by ring)]; rw [LinearMap.comp_apply]; rw [ofValEqZeroAux_prop]
    exact x.prop (by lia)

@[simp]

Depends on / 依赖: Eq.refl, ofValEqZeroAux
-/
def ofValEqZero {n : Nat} {x : AdicCompletion I M} (hxn : x.val n = 0) :
    AdicCompletion I ↥(I ^ n • (⊤ : Submodule R M)) where
  val i := ofValEqZeroAux I (Eq.refl (i + n)) hxn
  property {i j} h := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← (powSMulQuotInclusion_injective I rfl ⊤).eq_iff]; rw [ofValEqZeroAux_prop]; rw [← LinearMap.comp_apply]; rw [← factorPow_comp_powSMulQuotInclusion I rfl
      (show i + k + n = k + (i + n) by ring)]; rw [LinearMap.comp_apply]; rw [ofValEqZeroAux_prop]
    exact x.prop (by lia)

@[simp]
/--
theorem `ofPowSMul_ofValEqZero` / 定理 `ofPowSMul_ofValEqZero`

English:
theorem ofPowSMul_ofValEqZero
  given: {n : Nat} {x : AdicCompletion I M} (hxn : x.val n = 0)
  proof: by
  ext i; by_cases! h : n <= i
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
    rw [ofPowSMul_val_apply _ rfl]; rw [ofValEqZero]; rw [ofValEqZeroAux_prop]
  rw [ofPowSMul_val_apply_eq_zero _ h.le]; rw [← x.prop h.le]; rw [hxn]; rw [_root_.map_zero]

中文:
定理 ofPowSMul_ofValEqZero
  条件: {n : 自然数} {x : AdicCompletion I M} (hxn : x.val n = 0)
  证明: by
  ext i; by_cases! h : n <= i
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
    rw [ofPowSMul_val_apply _ rfl]; rw [ofValEqZero]; rw [ofValEqZeroAux_prop]
  rw [ofPowSMul_val_apply_eq_zero _ h.le]; rw [← x.prop h.le]; rw [hxn]; rw [_root_.map_zero]

Depends on / 依赖: Nat.exists_eq_add_of_le, _root_, _root_.map_zero, exists_eq_add_of_le, h.le, map_zero, ofPowSMul_val_apply, ofPowSMul_val_apply_eq_zero, ofValEqZero, ofValEqZeroAux_prop, x.prop
-/
theorem ofPowSMul_ofValEqZero {n : Nat} {x : AdicCompletion I M} (hxn : x.val n = 0) :
    ofPowSMul I M n (ofValEqZero I hxn) = x := by
  ext i; by_cases! h : n <= i
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
    rw [ofPowSMul_val_apply _ rfl]; rw [ofValEqZero]; rw [ofValEqZeroAux_prop]
  rw [ofPowSMul_val_apply_eq_zero _ h.le]; rw [← x.prop h.le]; rw [hxn]; rw [_root_.map_zero]

/--
theorem `restrictScalars_range_ofPowSMul_eq_ker_eval` / 定理 `restrictScalars_range_ofPowSMul_eq_ker_eval`

English:
theorem restrictScalars_range_ofPowSMul_eq_ker_eval
  given: {n : Nat}
  proof: by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rcases hx with ⟨y, rfl⟩
    rw [LinearMap.mem_ker]; rw [eval_apply]; rw [ofPowSMul_val_apply_eq_zero _ (by rfl)]
  simp only [LinearMap.mem_ker, coe_eval] at hx
  use ofValEqZero I hx; simp

中文:
定理 restrictScalars_range_ofPowSMul_eq_ker_eval
  条件: {n : 自然数}
  证明: by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rcases hx with ⟨y, rfl⟩
    rw [LinearMap.mem_ker]; rw [eval_apply]; rw [ofPowSMul_val_apply_eq_zero _ (by rfl)]
  simp only [LinearMap.mem_ker, coe_eval] at hx
  use ofValEqZero I hx; simp

Depends on / 依赖: LinearMap, LinearMap.mem_ker, coe_eval, eval_apply, le_antisymm, mem_ker, ofPowSMul_val_apply_eq_zero, ofValEqZero
-/
theorem restrictScalars_range_ofPowSMul_eq_ker_eval {n : Nat} :
    (ofPowSMul I M n).range.restrictScalars R = (eval I M n).ker := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rcases hx with ⟨y, rfl⟩
    rw [LinearMap.mem_ker]; rw [eval_apply]; rw [ofPowSMul_val_apply_eq_zero _ (by rfl)]
  simp only [LinearMap.mem_ker, coe_eval] at hx
  use ofValEqZero I hx; simp

/--
lemma `lsum_smul_comp_finsuppLEquivDirectSum_symm` / 引理 `lsum_smul_comp_finsuppLEquivDirectSum_symm`

English:
lemma lsum_smul_comp_finsuppLEquivDirectSum_symm
  statement: {ι : Type*} [DecidableEq ι] [Fintype ι]
  proof: by
  ext
  -- simp [-algebraMap_smul, algebraMap_apply, -smul_eq_mul]
  simp only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, LinearMap.coe_comp,
    coe_lsum, LinearMap.coe_smul, LinearMap.id_coe, LinearEquiv.coe_coe, Function.comp_apply,
    finsuppLEquivDirectSum_symm_lof, Pi.smul_apply, id_eq, smul_zero, sum_single_index, smul_eval,
    mapQ_eq_factor, factor_eq_factor, of_apply, mkQ_apply, Ideal.Quotient.mk_eq_mk, mk_apply_coe,
    sumEquivOfFintype_apply, sum_lof, map_mk, AdicCauchySequence.map_apply_coe, map_smul]
  rw [← Ideal.Quotient.algebraMap_eq]; rw [algebraMap_smul]

中文:
引理 lsum_smul_comp_finsuppLEquivDirectSum_symm
  结论: {ι : 类型} [DecidableEq ι] [有限类型 ι]
  证明: by
  ext
  -- simp [-algebraMap_smul, algebraMap_apply, -smul_eq_mul]
  simp only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, LinearMap.coe_comp,
    coe_lsum, LinearMap.coe_smul, LinearMap.id_coe, LinearEquiv.coe_coe, Function.comp_apply,
    finsuppLEquivDirectSum_symm_lof, Pi.smul_apply, id_eq, smul_zero, sum_single_index, smul_eval,
    mapQ_eq_factor, factor_eq_factor, of_apply, mkQ_apply, Ideal.Quotient.mk_eq_mk, mk_apply_coe,
    sumEquivOfFintype_apply, sum_lof, map_mk, AdicCauchySequence.map_apply_coe, map_smul]
  rw [← Ideal.Quotient.algebraMap_eq]; rw [algebraMap_smul]
-/
private lemma lsum_smul_comp_finsuppLEquivDirectSum_symm {ι : Type*} [DecidableEq ι] [Fintype ι]
    (f : ι -> R) : ((lsum (AdicCompletion I R))
      fun i => ((algebraMap R (AdicCompletion I R)) (f i) • .id :
        AdicCompletion I M ->ₗ[AdicCompletion I R] AdicCompletion I M)) ∘ₗ
      (finsuppLEquivDirectSum (AdicCompletion I R) (AdicCompletion I M) ι).symm.toLinearMap =
    (map I (lsum R fun i => f i • .id) ∘ₗ map I (finsuppLEquivDirectSum R M ι).symm.toLinearMap) ∘ₗ
      (sumEquivOfFintype I (fun _ : ι => M)) := by
  ext
  -- simp [-algebraMap_smul, algebraMap_apply, -smul_eq_mul]
  simp only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, LinearMap.coe_comp,
    coe_lsum, LinearMap.coe_smul, LinearMap.id_coe, LinearEquiv.coe_coe, Function.comp_apply,
    finsuppLEquivDirectSum_symm_lof, Pi.smul_apply, id_eq, smul_zero, sum_single_index, smul_eval,
    mapQ_eq_factor, factor_eq_factor, of_apply, mkQ_apply, Ideal.Quotient.mk_eq_mk, mk_apply_coe,
    sumEquivOfFintype_apply, sum_lof, map_mk, AdicCauchySequence.map_apply_coe, map_smul]
  rw [← Ideal.Quotient.algebraMap_eq]; rw [algebraMap_smul]

set_option backward.isDefEq.respectTransparency.types false in
variable {I} in
@[stacks 05GG "(2)"]
/--
theorem `pow_smul_top_eq_ker_eval` / 定理 `pow_smul_top_eq_ker_eval`

English:
theorem pow_smul_top_eq_ker_eval
  given: {n : Nat} (h : I.FG)
  statement: I ^ n • ⊤ = (eval I M n).ker
  proof: by
  classical
  refine le_antisymm (pow_smul_top_le_ker_eval ..) ?_
  replace h := Ideal.FG.pow (n := n) h
  rcases h with ⟨s, hs⟩
  simp only [← hs, span_smul_eq]
  rw [← restrictScalars_top R (AdicCompletion I R) (AdicCompletion I M)]; rw [← restrictScalars_image_smul_eq (R := AdicCompletion I R)]; rw [← restrictScalars_range_ofPowSMul_eq_ker_eval]; rw [restrictScalars_le]; rw [image_smul_top_eq_range_lsum]
  simp only [SetLike.coe_sort_coe]
  rw [← LinearMap.range_comp_of_range_eq_top (f := (finsuppLEquivDirectSum ..).symm.toLinearMap)
    _ (by simp)]; rw [lsum_smul_comp_finsuppLEquivDirectSum_symm]; rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]; rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _ <|
      Function.RightInverse.surjective (g := map I (finsuppLEquivDirectSum R M s)) (fun _ => by
      simp [← LinearMap.comp_apply]; rw [map_comp]))]
  rintro _ ⟨x, rfl⟩
  have : Function.Surjective ((lsum R fun i : s => i.val • (LinearMap.id : M ->ₗ[R] M)).codRestrict
    (I ^ n • ⊤) (fun _ => by simp [← hs, span_smul_eq, smul_top_eq_range_lsum])) := by
    rw [← LinearMap.range_eq_top]; rw [LinearMap.range_codRestrict]; rw [← hs]; rw [span_smul_eq]; rw [smul_top_eq_range_lsum]
    simp
  rcases map_surjective I this x with ⟨x, rfl⟩
  exact ⟨x, by rw [← LinearMap.comp_apply, map_comp, LinearMap.subtype_comp_codRestrict]⟩

中文:
定理 pow_smul_top_eq_ker_eval
  条件: {n : 自然数} (h : I.FG)
  结论: I ^ n • ⊤ = (eval I M n).ker
  证明: by
  classical
  refine le_antisymm (pow_smul_top_le_ker_eval ..) ?_
  replace h := Ideal.FG.pow (n := n) h
  rcases h with ⟨s, hs⟩
  simp only [← hs, span_smul_eq]
  rw [← restrictScalars_top R (AdicCompletion I R) (AdicCompletion I M)]; rw [← restrictScalars_image_smul_eq (R := AdicCompletion I R)]; rw [← restrictScalars_range_ofPowSMul_eq_ker_eval]; rw [restrictScalars_le]; rw [image_smul_top_eq_range_lsum]
  simp only [SetLike.coe_sort_coe]
  rw [← LinearMap.range_comp_of_range_eq_top (f := (finsuppLEquivDirectSum ..).symm.toLinearMap)
    _ (by simp)]; rw [lsum_smul_comp_finsuppLEquivDirectSum_symm]; rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]; rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _ <|
      Function.RightInverse.surjective (g := map I (finsuppLEquivDirectSum R M s)) (fun _ => by
      simp [← LinearMap.comp_apply]; rw [map_comp]))]
  rintro _ ⟨x, rfl⟩
  have : Function.Surjective ((lsum R fun i : s => i.val • (LinearMap.id : M ->ₗ[R] M)).codRestrict
    (I ^ n • ⊤) (fun _ => by simp [← hs, span_smul_eq, smul_top_eq_range_lsum])) := by
    rw [← LinearMap.range_eq_top]; rw [LinearMap.range_codRestrict]; rw [← hs]; rw [span_smul_eq]; rw [smul_top_eq_range_lsum]
    simp
  rcases map_surjective I this x with ⟨x, rfl⟩
  exact ⟨x, by rw [← LinearMap.comp_apply, map_comp, LinearMap.subtype_comp_codRestrict]⟩

Depends on / 依赖: AdicCompletion, Ideal.FG.pow, LinearMap, LinearMap.range_comp_of_range_eq_top, SetLike, SetLike.coe_sort_coe, classical, coe_sort_coe, finsuppLEquivDi, image_smul_top_eq_range_lsum, le_antisymm, pow_smul_top_le_ker_eval, range_comp_of_range_eq_top, replace, restrictScalars_image_smul_eq, restrictScalars_le, restrictScalars_range_ofPowSMul_eq_ker_eval, restrictScalars_top, span_smul_eq
-/
theorem pow_smul_top_eq_ker_eval {n : Nat} (h : I.FG) : I ^ n • ⊤ = (eval I M n).ker := by
  classical
  refine le_antisymm (pow_smul_top_le_ker_eval ..) ?_
  replace h := Ideal.FG.pow (n := n) h
  rcases h with ⟨s, hs⟩
  simp only [← hs, span_smul_eq]
  rw [← restrictScalars_top R (AdicCompletion I R) (AdicCompletion I M)]; rw [← restrictScalars_image_smul_eq (R := AdicCompletion I R)]; rw [← restrictScalars_range_ofPowSMul_eq_ker_eval]; rw [restrictScalars_le]; rw [image_smul_top_eq_range_lsum]
  simp only [SetLike.coe_sort_coe]
  rw [← LinearMap.range_comp_of_range_eq_top (f := (finsuppLEquivDirectSum ..).symm.toLinearMap)
    _ (by simp)]; rw [lsum_smul_comp_finsuppLEquivDirectSum_symm]; rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]; rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _ <|
      Function.RightInverse.surjective (g := map I (finsuppLEquivDirectSum R M s)) (fun _ => by
      simp [← LinearMap.comp_apply]; rw [map_comp]))]
  rintro _ ⟨x, rfl⟩
  have : Function.Surjective ((lsum R fun i : s => i.val • (LinearMap.id : M ->ₗ[R] M)).codRestrict
    (I ^ n • ⊤) (fun _ => by simp [← hs, span_smul_eq, smul_top_eq_range_lsum])) := by
    rw [← LinearMap.range_eq_top]; rw [LinearMap.range_codRestrict]; rw [← hs]; rw [span_smul_eq]; rw [smul_top_eq_range_lsum]
    simp
  rcases map_surjective I this x with ⟨x, rfl⟩
  exact ⟨x, by rw [← LinearMap.comp_apply, map_comp, LinearMap.subtype_comp_codRestrict]⟩

set_option backward.isDefEq.respectTransparency.types false in
variable {I} in
/-- `AdicCompletion I M` is adic complete when `I` is finitely generated. -/
@[stacks 05GG "(1)"]
/--
theorem `isAdicComplete` / 定理 `isAdicComplete`

English:
theorem isAdicComplete
  given: (h : I.FG)
  statement: IsAdicComplete I (AdicCompletion I M) where
  proof: by
    let L : AdicCompletion I M := {
      val i := (x i).val i
      property {m n} h' := by
        simp only [transitionMap_comp_eval_apply]
        specialize hx h'
        rwa [SModEq.sub_mem, pow_smul_top_eq_ker_eval h, LinearMap.mem_ker, _root_.map_sub,
          sub_eq_zero, eval_apply, eval_apply, eq_comm] at hx
    }
    use L; intro i
    rw [SModEq.sub_mem]; rw [pow_smul_top_eq_ker_eval h]
    simp [L]

中文:
定理 isAdicComplete
  条件: (h : I.FG)
  结论: 是AdicComplete I (AdicCompletion I M) where
  证明: by
    let L : AdicCompletion I M := {
      val i := (x i).val i
      property {m n} h' := by
        simp only [transitionMap_comp_eval_apply]
        specialize hx h'
        rwa [SModEq.sub_mem, pow_smul_top_eq_ker_eval h, LinearMap.mem_ker, _root_.map_sub,
          sub_eq_zero, eval_apply, eval_apply, eq_comm] at hx
    }
    use L; intro i
    rw [SModEq.sub_mem]; rw [pow_smul_top_eq_ker_eval h]
    simp [L]

Depends on / 依赖: AdicCompletion, LinearMap, LinearMap.mem_ker, SModEq, SModEq.sub_mem, _root_, _root_.map_sub, eq_comm, eval_apply, map_sub, mem_ker, pow_smul_top_eq_ker_eval, property, specialize, sub_eq_zero, sub_mem, transitionMap_comp_eval_apply
-/
theorem isAdicComplete (h : I.FG) : IsAdicComplete I (AdicCompletion I M) where
  prec' x hx := by
    let L : AdicCompletion I M := {
      val i := (x i).val i
      property {m n} h' := by
        simp only [transitionMap_comp_eval_apply]
        specialize hx h'
        rwa [SModEq.sub_mem, pow_smul_top_eq_ker_eval h, LinearMap.mem_ker, _root_.map_sub,
          sub_eq_zero, eval_apply, eval_apply, eq_comm] at hx
    }
    use L; intro i
    rw [SModEq.sub_mem]; rw [pow_smul_top_eq_ker_eval h]
    simp [L]

/--
lemma `ker_evalOneₐ_eq_map` / 引理 `ker_evalOneₐ_eq_map`

English:
lemma ker_evalOneₐ_eq_map
  given: (fg : I.FG)
  proof: by
  ext x
  trans x in (AdicCompletion.eval I R 1).ker
  · have eq : I ^ 1 * ⊤ = I := by simp
    have : Function.Injective (Ideal.Quotient.factor ((le_of_eq eq))) := by
      simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
        using Ideal.map_mk_eq_bot_of_le (le_of_eq eq.symm)
    simpa [← factorₐ_evalₐ_one, ← factor_eval_eq_evalₐ] using map_eq_zero_iff _ this
  · simp [← pow_smul_top_eq_ker_eval fg]

中文:
引理 ker_evalOneₐ_eq_map
  条件: (fg : I.FG)
  证明: by
  ext x
  trans x in (AdicCompletion.eval I R 1).ker
  · have eq : I ^ 1 * ⊤ = I := by simp
    have : Function.Injective (Ideal.Quotient.factor ((le_of_eq eq))) := by
      simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
        using Ideal.map_mk_eq_bot_of_le (le_of_eq eq.symm)
    simpa [← factorₐ_evalₐ_one, ← factor_eval_eq_evalₐ] using map_eq_zero_iff _ this
  · simp [← pow_smul_top_eq_ker_eval fg]

Depends on / 依赖: AdicCompletion, AdicCompletion.eval, Function, Function.Injective, Ideal.Quotient.factor, Ideal.Quotient.factor_ker, Ideal.map_mk_eq_bot_of_le, Injective, Quotient, RingHom, RingHom.injective_iff_ker_eq_bot, eq.symm, factor, factor_ker, injective_iff_ker_eq_bot, le_of_eq, map_eq_zero_iff, map_mk_eq_bot_of_le, pow_smul_top_eq_ker_eval
-/
lemma ker_evalOneₐ_eq_map (fg : I.FG) :
    RingHom.ker (evalOneₐ I).toRingHom = I.map (algebraMap R (AdicCompletion I R)) := by
  ext x
  trans x in (AdicCompletion.eval I R 1).ker
  · have eq : I ^ 1 * ⊤ = I := by simp
    have : Function.Injective (Ideal.Quotient.factor ((le_of_eq eq))) := by
      simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
        using Ideal.map_mk_eq_bot_of_le (le_of_eq eq.symm)
    simpa [← factorₐ_evalₐ_one, ← factor_eval_eq_evalₐ] using map_eq_zero_iff _ this
  · simp [← pow_smul_top_eq_ker_eval fg]

end AdicCompletion

namespace MvPowerSeries

instance {σ : Type*} [Finite σ] :
    IsAdicComplete (.span (.range X) : Ideal (MvPowerSeries σ R)) (MvPowerSeries σ R) := by
  have : Ideal.map (toAdicCompletionAlgEquiv σ R).toRingEquiv (Ideal.span (Set.range X)) =
    (MvPolynomial.idealOfVars σ R).map (algebraMap ..) := by
    simp_rw [Ideal.map_span, ← Set.range_comp]
    congr 2; ext1
    simp [AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X, toAdicCompletion_coe]
  rw [← IsAdicComplete.congr_ringEquiv _ (toAdicCompletionAlgEquiv σ R).toRingEquiv]; rw [this]; rw [IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete (MvPolynomial.idealOfVars_fg σ R)

end MvPowerSeries

namespace PowerSeries

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAdicComplete (.span {X} : Ideal (PowerSeries R)) (PowerSeries R)
  body: by
  have : IsAdicComplete (.span (.range MvPowerSeries.X) : Ideal (MvPowerSeries Unit R))
    (MvPowerSeries Unit R) := inferInstance
  rwa [Set.range_unique] at this

中文:
实例 :
  签名: 是AdicComplete (.span {X} : 理想 (幂级数 R)) (幂级数 R)
  定义体: by
  have : IsAdicComplete (.span (.range MvPowerSeries.X) : Ideal (MvPowerSeries Unit R))
    (MvPowerSeries Unit R) := inferInstance
  rwa [Set.range_unique] at this

Depends on / 依赖: IsAdicComplete, MvPowerSeries, MvPowerSeries.X, Set.range_unique, range_unique
-/
instance : IsAdicComplete (.span {X} : Ideal (PowerSeries R)) (PowerSeries R) := by
  have : IsAdicComplete (.span (.range MvPowerSeries.X) : Ideal (MvPowerSeries Unit R))
    (MvPowerSeries Unit R) := inferInstance
  rwa [Set.range_unique] at this

end PowerSeries
