/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Noetherian.Basic

/-!

# `Ext`-modules between finitely generated modules over Noetherian rings are finitely generated

-/

public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory Abelian

/--
Instance `ModuleCat.finite_ext` / 实例 `ModuleCat.finite_ext`

English:
instance ModuleCat.finite_ext
  signature: [Small.{v} R] [IsNoetherianRing R] (N M : ModuleCat.{v} R)
  body: by
  induction i generalizing N with
  | zero => exact Module.Finite.equiv (Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv).symm
  | succ n ih =>
    obtain ⟨N, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R N
    let exac := LinearMap.shortExact_shortComplexKer surjf
    exact Module

中文:
实例 模范畴.finite_ext
  签名: [Small.{v} R] [是Noether环 R] (N M : 模范畴.{v} R)
  定义体: by
  induction i generalizing N with
  | zero => exact Module.Finite.equiv (Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv).symm
  | succ n ih =>
    obtain ⟨N, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R N
    let exac := LinearMap.shortExact_shortComplexKer surjf
    exact Module

Depends on / 依赖: Ext.linearEquiv, Finite, LinearMap, LinearMap.shortExact_shortComplexKer, Module, Module.Finite.equiv, Module.Finite.of_surjective, Module.exists_finite_presentation, ModuleCat, ModuleCat.homLinearEquiv, add_comm, exac.extClass.precompOfLinear, exists_finite_presentation, extClass, generalizing, homLinearEquiv, of_surjective, precompOfLinear, shortExact_shortComplexKer
-/
instance ModuleCat.finite_ext [Small.{v} R] [IsNoetherianRing R] (N M : ModuleCat.{v} R)
    [Module.Finite R N] [Module.Finite R M] (i : Nat) : Module.Finite R (Ext N M i) := by
  induction i generalizing N with
  | zero => exact Module.Finite.equiv (Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv).symm
  | succ n ih =>
    obtain ⟨N, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R N
    let exac := LinearMap.shortExact_shortComplexKer surjf
    exact Module.Finite.of_surjective (exac.extClass.precompOfLinear R M (add_comm 1 n))
      (precomp_extClass_surjective_of_projective_X₂ M exac n)
