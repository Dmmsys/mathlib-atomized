/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Cusp form submodule and IsCuspForm predicate

This file defines the inclusion of cusp forms into modular forms as a linear map, the cusp form
submodule of modular forms, and the `IsCuspForm` predicate. It also provides a direct constructor
`ModularForm.toCuspForm` for building cusp forms from modular forms with vanishing constant
q-expansion coefficient (for `𝒮ℒ`).

## Main definitions

* `CuspForm.toModularFormₗ`: the inclusion `CuspForm Γ k →ₗ[ℂ] ModularForm Γ k`.
* `ModularForm.cuspFormSubmodule`: the submodule of `ModularForm Γ k` consisting of cusp forms.
* `ModularForm.IsCuspForm`: predicate that a modular form lies in the cusp form submodule.
* `ModularForm.toCuspForm`: builds a `CuspForm 𝒮ℒ k` from a `ModularForm` whose q-expansion
  has vanishing constant term.

## Main results

* `CuspForm.toModularFormₗ_injective`: the inclusion is injective.
* `CuspForm.equivCuspFormSubmodule`: `CuspForm Γ k ≃ₗ[ℂ] cuspFormSubmodule Γ k`.
* `ModularForm.isCuspForm_iff_coeffZero_eq_zero`: for `𝒮ℒ`, `IsCuspForm` is equivalent to the
  q-expansion having vanishing constant term.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm Complex SlashInvariantForm SlashInvariantFormClass
  ModularFormClass MatrixGroups OnePoint Filter Topology

variable {Γ : Subgroup (GL (Fin 2) Real)} {k : Int}

namespace CuspForm

/--
Definition of `toModularFormₗ` / `toModularFormₗ` 的定义

English:
definition toModularFormₗ
  signature: [Γ.HasDetOne]
  body: ModularFormClass.modularForm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

中文:
定义 toModularFormₗ
  签名: [Γ.有DetOne]
  定义体: ModularFormClass.modularForm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

Depends on / 依赖: ModularFormClass, ModularFormClass.modularForm, modularForm
-/
def toModularFormₗ [Γ.HasDetOne] : CuspForm Γ k ->ₗ[Complex] ModularForm Γ k where
  toFun := ModularFormClass.modularForm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/--
lemma `toModularFormₗ_apply` / 引理 `toModularFormₗ_apply`

English:
lemma toModularFormₗ_apply
  given: [Γ.HasDetOne] (f : CuspForm Γ k) (z : ℍ)
  proof: rfl

中文:
引理 toModularFormₗ_apply
  条件: [Γ.有DetOne] (f : 尖点形式 Γ k) (z : ℍ)
  证明: rfl
-/
lemma toModularFormₗ_apply [Γ.HasDetOne] (f : CuspForm Γ k) (z : ℍ) :
    (toModularFormₗ f) z = f z := rfl

/--
lemma `toModularFormₗ_eq_coe` / 引理 `toModularFormₗ_eq_coe`

English:
lemma toModularFormₗ_eq_coe
  given: [Γ.HasDetOne] (f : CuspForm Γ k)
  proof: rfl

中文:
引理 toModularFormₗ_eq_coe
  条件: [Γ.有DetOne] (f : 尖点形式 Γ k)
  证明: rfl
-/
lemma toModularFormₗ_eq_coe [Γ.HasDetOne] (f : CuspForm Γ k) :
    toModularFormₗ f = (f : ModularForm Γ k) := rfl

/--
lemma `toModularFormₗ_injective` / 引理 `toModularFormₗ_injective`

English:
lemma toModularFormₗ_injective
  given: [Γ.HasDetOne]
  proof: fun _ _ h => DFunLike.ext _ _ fun z => DFunLike.congr_fun h z

中文:
引理 toModularFormₗ_injective
  条件: [Γ.有DetOne]
  证明: fun _ _ h => DFunLike.ext _ _ fun z => DFunLike.congr_fun h z

Depends on / 依赖: DFunLike, DFunLike.congr_fun, DFunLike.ext, congr_fun
-/
lemma toModularFormₗ_injective [Γ.HasDetOne] :
    Function.Injective (toModularFormₗ : CuspForm Γ k -> ModularForm Γ k) :=
  fun _ _ h => DFunLike.ext _ _ fun z => DFunLike.congr_fun h z

end CuspForm

namespace ModularForm

/--
Definition of `cuspFormSubmodule` / `cuspFormSubmodule` 的定义

English:
definition cuspFormSubmodule
  signature: (Γ : Subgroup (GL (Fin 2) Real)) (k : Int) [Γ.HasDetOne]
  body: LinearMap.range CuspForm.toModularFormₗ

中文:
定义 cuspFormSubmodule
  签名: (Γ : 子群 (GL (有限集 2) 实数)) (k : 整数) [Γ.有DetOne]
  定义体: LinearMap.range CuspForm.toModularFormₗ

Depends on / 依赖: CuspForm, CuspForm.toModularForm, LinearMap, LinearMap.range
-/
def cuspFormSubmodule (Γ : Subgroup (GL (Fin 2) Real)) (k : Int) [Γ.HasDetOne] :
    Submodule Complex (ModularForm Γ k) :=
  LinearMap.range CuspForm.toModularFormₗ

/--
Definition of `IsCuspForm` / `IsCuspForm` 的定义

English:
definition IsCuspForm
  signature: [Γ.HasDetOne] (f : ModularForm Γ k)
  body: f in cuspFormSubmodule Γ k

@[simp]

中文:
定义 IsCuspForm
  签名: [Γ.有DetOne] (f : 模形式 Γ k)
  定义体: f in cuspFormSubmodule Γ k

@[simp]

Depends on / 依赖: cuspFormSubmodule
-/
def IsCuspForm [Γ.HasDetOne] (f : ModularForm Γ k) : Prop :=
  f in cuspFormSubmodule Γ k

@[simp]
/--
lemma `mem_cuspFormSubmodule_iff` / 引理 `mem_cuspFormSubmodule_iff`

English:
lemma mem_cuspFormSubmodule_iff
  given: [Γ.HasDetOne] {f : ModularForm Γ k}
  proof: Iff.rfl

中文:
引理 mem_cuspFormSubmodule_iff
  条件: [Γ.有DetOne] {f : 模形式 Γ k}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_cuspFormSubmodule_iff [Γ.HasDetOne] {f : ModularForm Γ k} :
    f in cuspFormSubmodule Γ k ↔ IsCuspForm f := Iff.rfl

/--
Definition of `CuspForm.equivCuspFormSubmodule` / `CuspForm.equivCuspFormSubmodule` 的定义

English:
definition CuspForm.equivCuspFormSubmodule
  signature: (Γ : Subgroup (GL (Fin 2) Real)) (k : Int) [Γ.HasDetOne]
  body: LinearEquiv.ofInjective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

中文:
定义 尖点形式.equivCuspFormSubmodule
  签名: (Γ : 子群 (GL (有限集 2) 实数)) (k : 整数) [Γ.有DetOne]
  定义体: LinearEquiv.ofInjective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

Depends on / 依赖: CuspForm, CuspForm.toModularForm, LinearEquiv, LinearEquiv.ofInjective, ofInjective
-/
def CuspForm.equivCuspFormSubmodule (Γ : Subgroup (GL (Fin 2) Real)) (k : Int) [Γ.HasDetOne] :
    CuspForm Γ k ≃ₗ[Complex] cuspFormSubmodule Γ k :=
  LinearEquiv.ofInjective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

/--
lemma `CuspForm.isCuspForm_toModularFormₗ` / 引理 `CuspForm.isCuspForm_toModularFormₗ`

English:
lemma CuspForm.isCuspForm_toModularFormₗ
  statement: {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetOne]
  proof: by
  simp [← mem_cuspFormSubmodule_iff, ModularForm.cuspFormSubmodule]

中文:
引理 尖点形式.isCuspForm_toModularFormₗ
  结论: {Γ : 子群 (GL (有限集 2) 实数)} [Γ.有DetOne]
  证明: by
  simp [← mem_cuspFormSubmodule_iff, ModularForm.cuspFormSubmodule]

Depends on / 依赖: ModularForm, ModularForm.cuspFormSubmodule, cuspFormSubmodule, mem_cuspFormSubmodule_iff
-/
lemma CuspForm.isCuspForm_toModularFormₗ {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetOne]
    (f : CuspForm Γ k) : ModularForm.IsCuspForm f.toModularFormₗ := by
  simp [← mem_cuspFormSubmodule_iff, ModularForm.cuspFormSubmodule]

/--
lemma `isCuspForm_iff` / 引理 `isCuspForm_iff`

English:
lemma isCuspForm_iff
  given: [Γ.HasDetOne] (f : ModularForm Γ k)
  proof: ⟨fun ⟨g, hg⟩ _ => hg ▸ g.zero_at_cusps', fun h => ⟨⟨f, f.holo', h⟩, rfl⟩⟩

中文:
引理 isCuspForm_iff
  条件: [Γ.有DetOne] (f : 模形式 Γ k)
  证明: ⟨fun ⟨g, hg⟩ _ => hg ▸ g.zero_at_cusps', fun h => ⟨⟨f, f.holo', h⟩, rfl⟩⟩

Depends on / 依赖: f.holo, g.zero_at_cusps, zero_at_cusps
-/
lemma isCuspForm_iff [Γ.HasDetOne] (f : ModularForm Γ k) :
    IsCuspForm f ↔ forall {c}, IsCusp c Γ -> c.IsZeroAt f k :=
  ⟨fun ⟨g, hg⟩ _ => hg ▸ g.zero_at_cusps', fun h => ⟨⟨f, f.holo', h⟩, rfl⟩⟩

/--
lemma `isZeroAtImInfty_of_valueAtInfty_eq_zero` / 引理 `isZeroAtImInfty_of_valueAtInfty_eq_zero`

English:
lemma isZeroAtImInfty_of_valueAtInfty_eq_zero
  statement: {F : Type*} [FunLike F ℍ Complex]
  proof: by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have hΓ : Γ.strictWidthInfty in Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  have hanal := ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
  have hper := periodic_comp_ofComplex f hΓ
  simp_rw [IsZeroAtImInfty, ZeroAtFilter, ← h, ← cuspFunction_apply_zero hh hanal hper]
  exact (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)).congr
    (fun τ => SlashInvariantFormClass.eq_cuspFunction f τ hΓ hh.ne')

中文:
引理 isZeroAtImInfty_of_valueAtInfty_eq_zero
  结论: {F : 类型} [函数状 F ℍ 复形]
  证明: by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have hΓ : Γ.strictWidthInfty in Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  have hanal := ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
  have hper := periodic_comp_ofComplex f hΓ
  simp_rw [IsZeroAtImInfty, ZeroAtFilter, ← h, ← cuspFunction_apply_zero hh hanal hper]
  exact (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)).congr
    (fun τ => SlashInvariantFormClass.eq_cuspFunction f τ hΓ hh.ne')

Depends on / 依赖: Fact.out, IsZeroAtImInfty, ModularFormClass, ModularFormClass.analyticAt_cuspFunction_zero, SlashInvariantFormClass, SlashInvariantFormClass.eq_cuspFunction, ZeroAtFilter, analyticAt_cuspFunction_zero, continuousAt, cuspFunction_apply_zero, eq_cuspFunction, hanal.continuousAt.tendsto.comp, hh.n, periodic_comp_ofComplex, qParam_tendsto_atImInfty, simp_rw, strictPeriods, strictWidthInfty, strictWidthInfty_mem_strictPeriods, strictWidthInfty_pos_iff
-/
lemma isZeroAtImInfty_of_valueAtInfty_eq_zero {F : Type*} [FunLike F ℍ Complex]
    [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] [Fact (IsCusp ∞ Γ)] [ModularFormClass F Γ k]
    (f : F) (h : valueAtInfty f = 0) : IsZeroAtImInfty f := by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have hΓ : Γ.strictWidthInfty in Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  have hanal := ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
  have hper := periodic_comp_ofComplex f hΓ
  simp_rw [IsZeroAtImInfty, ZeroAtFilter, ← h, ← cuspFunction_apply_zero hh hanal hper]
  exact (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)).congr
    (fun τ => SlashInvariantFormClass.eq_cuspFunction f τ hΓ hh.ne')

section SL2Z

variable {k : Int}

/--
lemma `isZeroAt_of_coeffZero_eq_zero` / 引理 `isZeroAt_of_coeffZero_eq_zero`

English:
lemma isZeroAt_of_coeffZero_eq_zero
  statement: (f : ModularForm 𝒮ℒ k)
  proof: by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  rw [show (⇑f ∣[k] γ) = ⇑f from f.slash_action_eq' _ ⟨γ, rfl⟩]
exact isZeroAtImInfty_of_valueAtInfty_eq_zero f by
    rwa [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
      (periodic_comp_ofComplex f one_mem_strictPeriods_SL)]

中文:
引理 isZeroAt_of_coeffZero_eq_zero
  结论: (f : 模形式 𝒮ℒ k)
  证明: by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  rw [show (⇑f ∣[k] γ) = ⇑f from f.slash_action_eq' _ ⟨γ, rfl⟩]
exact isZeroAtImInfty_of_valueAtInfty_eq_zero f by
    rwa [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
      (periodic_comp_ofComplex f one_mem_strictPeriods_SL)]

Depends on / 依赖: IsArithmetic, ModularFormClass, ModularFormClass.analyticAt_cuspFunction_zero, Subgroup, Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, analyticAt_cuspFunction_zero, f.slash_action_eq, isCusp_iff_isCusp_SL2Z, isZeroAtImInfty_of_valueAtInfty_eq_zero, isZeroAt_iff_forall_SL2Z, one_mem_strictPeriods_SL, one_pos, periodic_comp_ofComplex, qExpansion_coeff_zero, slash_action_eq
-/
lemma isZeroAt_of_coeffZero_eq_zero (f : ModularForm 𝒮ℒ k)
    (h : (qExpansion 1 f).coeff 0 = 0) {c : OnePoint Real} (hc : IsCusp c 𝒮ℒ) :
    c.IsZeroAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  rw [show (⇑f ∣[k] γ) = ⇑f from f.slash_action_eq' _ ⟨γ, rfl⟩]
exact isZeroAtImInfty_of_valueAtInfty_eq_zero f by
    rwa [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
      (periodic_comp_ofComplex f one_mem_strictPeriods_SL)]

/--
Definition of `toCuspForm` / `toCuspForm` 的定义

English:
definition toCuspForm
  signature: (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0)
  body: { f with zero_at_cusps' := isZeroAt_of_coeffZero_eq_zero f h }

@[simp]

中文:
定义 toCuspForm
  签名: (f : 模形式 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0)
  定义体: { f with zero_at_cusps' := isZeroAt_of_coeffZero_eq_zero f h }

@[simp]

Depends on / 依赖: isZeroAt_of_coeffZero_eq_zero, zero_at_cusps
-/
def toCuspForm (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0) : CuspForm 𝒮ℒ k :=
  { f with zero_at_cusps' := isZeroAt_of_coeffZero_eq_zero f h }

@[simp]
/--
lemma `toCuspForm_apply` / 引理 `toCuspForm_apply`

English:
lemma toCuspForm_apply
  statement: (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0)
  proof: rfl

中文:
引理 toCuspForm_apply
  结论: (f : 模形式 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0)
  证明: rfl
-/
lemma toCuspForm_apply (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0)
    (z : ℍ) : (toCuspForm f h) z = f z := rfl

/--
lemma `isCuspForm_iff_coeffZero_eq_zero` / 引理 `isCuspForm_iff_coeffZero_eq_zero`

English:
lemma isCuspForm_iff_coeffZero_eq_zero
  given: (f : ModularForm 𝒮ℒ k)
  proof: by
  refine ⟨fun ⟨g, hg⟩ => ?_, fun h => (isCuspForm_iff f).mpr (isZeroAt_of_coeffZero_eq_zero f h)⟩
  rw [← hg]; rw [qExpansion_coeff_zero one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL)
    (periodic_comp_ofComplex _ one_mem_strictPeriods_SL)]
  exact (CuspFormClass.zero_at_infty g).valueAtInfty_eq_zero

中文:
引理 isCuspForm_iff_coeffZero_eq_zero
  条件: (f : 模形式 𝒮ℒ k)
  证明: by
  refine ⟨fun ⟨g, hg⟩ => ?_, fun h => (isCuspForm_iff f).mpr (isZeroAt_of_coeffZero_eq_zero f h)⟩
  rw [← hg]; rw [qExpansion_coeff_zero one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL)
    (periodic_comp_ofComplex _ one_mem_strictPeriods_SL)]
  exact (CuspFormClass.zero_at_infty g).valueAtInfty_eq_zero

Depends on / 依赖: CuspFormClass, CuspFormClass.zero_at_infty, ModularFormClass, ModularFormClass.analyticAt_cuspFunction_zero, analyticAt_cuspFunction_zero, isCuspForm_iff, isZeroAt_of_coeffZero_eq_zero, one_mem_strictPeriods_SL, one_pos, periodic_comp_ofComplex, qExpansion_coeff_zero, valueAtInfty_eq_zero, zero_at_infty
-/
lemma isCuspForm_iff_coeffZero_eq_zero (f : ModularForm 𝒮ℒ k) :
    IsCuspForm f ↔ (qExpansion 1 f).coeff 0 = 0 := by
  refine ⟨fun ⟨g, hg⟩ => ?_, fun h => (isCuspForm_iff f).mpr (isZeroAt_of_coeffZero_eq_zero f h)⟩
  rw [← hg]; rw [qExpansion_coeff_zero one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL)
    (periodic_comp_ofComplex _ one_mem_strictPeriods_SL)]
  exact (CuspFormClass.zero_at_infty g).valueAtInfty_eq_zero

/--
lemma `sub_smul_isCuspForm` / 引理 `sub_smul_isCuspForm`

English:
lemma sub_smul_isCuspForm
  statement: (f g : ModularForm 𝒮ℒ k)
  proof: by
  rw [isCuspForm_iff_coeffZero_eq_zero]; rw [FunLike.coe_sub]; rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]; rw [FunLike.coe_smul]; rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]; rw [map_sub]; rw [PowerSeries.coeff_smul]
  simp [hg]

中文:
引理 sub_smul_isCuspForm
  结论: (f g : 模形式 𝒮ℒ k)
  证明: by
  rw [isCuspForm_iff_coeffZero_eq_zero]; rw [FunLike.coe_sub]; rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]; rw [FunLike.coe_smul]; rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]; rw [map_sub]; rw [PowerSeries.coeff_smul]
  simp [hg]

Depends on / 依赖: FunLike, FunLike.coe_smul, FunLike.coe_sub, ModularForm, ModularForm.qExpansion_smul, ModularForm.qExpansion_sub, PowerSeries, PowerSeries.coeff_smul, coe_smul, coe_sub, coeff_smul, isCuspForm_iff_coeffZero_eq_zero, map_sub, one_mem_strictPeriods_SL, one_pos, qExpansion_smul, qExpansion_sub
-/
lemma sub_smul_isCuspForm (f g : ModularForm 𝒮ℒ k)
    (hg : (qExpansion 1 g).coeff 0 = 1) :
    ModularForm.IsCuspForm (f - (qExpansion 1 f).coeff 0 • g) := by
  rw [isCuspForm_iff_coeffZero_eq_zero]; rw [FunLike.coe_sub]; rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]; rw [FunLike.coe_smul]; rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]; rw [map_sub]; rw [PowerSeries.coeff_smul]
  simp [hg]

end SL2Z

end ModularForm
