/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.MDifferentiable

/-!
# Eisenstein series are Modular Forms

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are Modular Forms.

## TODO

Add q-expansions and prove that they are not all identically zero.
-/

@[expose] public section

noncomputable section

namespace ModularForm

open EisensteinSeries CongruenceSubgroup MatrixGroups

/--
Definition of `eisensteinSeriesMF` / `eisensteinSeriesMF` 的定义

English:
definition eisensteinSeriesMF
  signature: {k : Int} {N : Nat} [NeZero N] (hk : 3 <= k) (a : Fin 2 -> ZMod N)
  body: eisensteinSeriesSIF a k
  slash_action_eq' := (eisensteinSeriesSIF a k).slash_action_eq'
  holo' := eisensteinSeriesSIF_mdifferentiable hk a
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ hγ => isBoundedAtImInfty_eisensteinSeriesSIF a hk γ

@[deprecated (since := "2026-02-10")] noncomputable alias eisensteinSeries_MF := eisensteinSeriesMF

中文:
定义 eisensteinSeriesMF
  签名: {k : 整数} {N : 自然数} [NeZero N] (hk : 3 <= k) (a : 有限集 2 -> ZMod N)
  定义体: eisensteinSeriesSIF a k
  slash_action_eq' := (eisensteinSeriesSIF a k).slash_action_eq'
  holo' := eisensteinSeriesSIF_mdifferentiable hk a
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ hγ => isBoundedAtImInfty_eisensteinSeriesSIF a hk γ

@[deprecated (since := "2026-02-10")] noncomputable alias eisensteinSeries_MF := eisensteinSeriesMF

Depends on / 依赖: eisensteinSeriesSIF
-/
def eisensteinSeriesMF {k : Int} {N : Nat} [NeZero N] (hk : 3 <= k) (a : Fin 2 -> ZMod N) :
    ModularForm Γ(N) k where
  toFun := eisensteinSeriesSIF a k
  slash_action_eq' := (eisensteinSeriesSIF a k).slash_action_eq'
  holo' := eisensteinSeriesSIF_mdifferentiable hk a
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ hγ => isBoundedAtImInfty_eisensteinSeriesSIF a hk γ

@[deprecated (since := "2026-02-10")] noncomputable alias eisensteinSeries_MF := eisensteinSeriesMF

/--
Definition of `E` / `E` 的定义

English:
definition E
  signature: {k : Nat} (hk : 3 <= k)
  body: ((1 / 2 : Complex) • eisensteinSeriesMF (mod_cast hk) 0).copy _ rfl Gamma_one_coe_eq_SL.symm

中文:
定义 E
  签名: {k : 自然数} (hk : 3 <= k)
  定义体: ((1 / 2 : Complex) • eisensteinSeriesMF (mod_cast hk) 0).copy _ rfl Gamma_one_coe_eq_SL.symm

Depends on / 依赖: Gamma_one_coe_eq_SL, Gamma_one_coe_eq_SL.symm, eisensteinSeriesMF, mod_cast
-/
def E {k : Nat} (hk : 3 <= k) : ModularForm 𝒮ℒ k :=
  ((1 / 2 : Complex) • eisensteinSeriesMF (mod_cast hk) 0).copy _ rfl Gamma_one_coe_eq_SL.symm

/--
Definition of `E₄` / `E₄` 的定义

English:
abbreviation E₄
  signature: : ModularForm 𝒮ℒ 4
  body: E (by norm_num : 3 <= 4)

中文:
缩写 E₄
  签名: : 模形式 𝒮ℒ 4
  定义体: E (by norm_num : 3 <= 4)
-/
abbrev E₄ : ModularForm 𝒮ℒ 4 := E (by norm_num : 3 <= 4)

/--
Definition of `E₆` / `E₆` 的定义

English:
abbreviation E₆
  signature: : ModularForm 𝒮ℒ 6
  body: E (by norm_num : 3 <= 6)

中文:
缩写 E₆
  签名: : 模形式 𝒮ℒ 6
  定义体: E (by norm_num : 3 <= 6)
-/
abbrev E₆ : ModularForm 𝒮ℒ 6 := E (by norm_num : 3 <= 6)

end ModularForm
