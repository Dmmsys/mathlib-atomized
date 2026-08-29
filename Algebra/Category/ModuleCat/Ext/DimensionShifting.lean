/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Continuity

/-!

# Dimension Shifting

-/

public section

universe v u

variable {R : Type u} [Ring R]

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

open CategoryTheory Abelian

/--
Definition of `ModuleCat.projectiveShortComplex` / `ModuleCat.projectiveShortComplex` 的定义

English:
abbreviation ModuleCat.projectiveShortComplex
  signature: [Small.{v} R] (M : ModuleCat.{v} R)
  body: let e : Module.Basis M R (M ->₀ Shrink.{v} R) :=
    ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)⟩
  (e.constr Nat id).shortComplexKer

中文:
缩写 模范畴.projectiveShortComplex
  签名: [Small.{v} R] (M : 模范畴.{v} R)
  定义体: let e : Module.Basis M R (M ->₀ Shrink.{v} R) :=
    ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)⟩
  (e.constr Nat id).shortComplexKer

Depends on / 依赖: Finsupp, Finsupp.mapRange.linearEquiv, Module, Module.Basis, Shrink, Shrink.linearEquiv, constr, e.constr, linearEquiv, mapRange, shortComplexKer
-/
noncomputable abbrev ModuleCat.projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    ShortComplex (ModuleCat.{v} R) :=
  let e : Module.Basis M R (M ->₀ Shrink.{v} R) :=
    ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)⟩
  (e.constr Nat id).shortComplexKer

/--
theorem `ModuleCat.shortExact_projectiveShortComplex` / 定理 `ModuleCat.shortExact_projectiveShortComplex`

English:
theorem ModuleCat.shortExact_projectiveShortComplex
  given: [Small.{v} R] (M : ModuleCat.{v} R)
  proof: by
  apply LinearMap.shortExact_shortComplexKer
  refine fun m => ⟨Finsupp.single m 1, ?_⟩
  simp [Module.Basis.constr_apply]

中文:
定理 模范畴.shortExact_projectiveShortComplex
  条件: [Small.{v} R] (M : 模范畴.{v} R)
  证明: by
  apply LinearMap.shortExact_shortComplexKer
  refine fun m => ⟨Finsupp.single m 1, ?_⟩
  simp [Module.Basis.constr_apply]

Depends on / 依赖: Finsupp, Finsupp.single, LinearMap, LinearMap.shortExact_shortComplexKer, Module, Module.Basis.constr_apply, constr_apply, shortExact_shortComplexKer, single
-/
theorem ModuleCat.shortExact_projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    M.projectiveShortComplex.ShortExact := by
  apply LinearMap.shortExact_shortComplexKer
  refine fun m => ⟨Finsupp.single m 1, ?_⟩
  simp [Module.Basis.constr_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{v}
  signature: R] (M
  body: Module.Free.finsupp R _ _

中文:
实例 [Small.{v}
  签名: R] (M
  定义体: Module.Free.finsupp R _ _

Depends on / 依赖: Module, Module.Free.finsupp, finsupp
-/
instance [Small.{v} R] (M : ModuleCat.{v} R) : Module.Free R M.projectiveShortComplex.X₂ :=
  Module.Free.finsupp R _ _

/--
theorem `precomp_extClass_surjective_of_projective_X₂` / 定理 `precomp_extClass_surjective_of_projective_X₂`

English:
theorem precomp_extClass_surjective_of_projective_X₂
  statement: [Small.{v} R]
  proof: fun x => Ext.contravariant_sequence_exact₃ h M x (Ext.eq_zero_of_projective _) (add_comm 1 n)

中文:
定理 precomp_extClass_surjective_of_projective_X₂
  结论: [Small.{v} R]
  证明: fun x => Ext.contravariant_sequence_exact₃ h M x (Ext.eq_zero_of_projective _) (add_comm 1 n)

Depends on / 依赖: Ext.contravariant_sequence_exact, Ext.eq_zero_of_projective, add_comm, eq_zero_of_projective
-/
theorem precomp_extClass_surjective_of_projective_X₂ [Small.{v} R]
    (M : ModuleCat.{v} R) {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (n : Nat)
    [Projective S.X₂] : Function.Surjective (h.extClass.precomp M (add_comm 1 n)) :=
  fun x => Ext.contravariant_sequence_exact₃ h M x (Ext.eq_zero_of_projective _) (add_comm 1 n)

/--
theorem `postcomp_extClass_surjective_of_projective_X₂` / 定理 `postcomp_extClass_surjective_of_projective_X₂`

English:
theorem postcomp_extClass_surjective_of_projective_X₂
  statement: [Small.{v} R]
  proof: fun x => Ext.covariant_sequence_exact₁ M h x (Ext.eq_zero_of_injective _) rfl

中文:
定理 postcomp_extClass_surjective_of_projective_X₂
  结论: [Small.{v} R]
  证明: fun x => Ext.covariant_sequence_exact₁ M h x (Ext.eq_zero_of_injective _) rfl

Depends on / 依赖: Ext.covariant_sequence_exact, Ext.eq_zero_of_injective, eq_zero_of_injective
-/
theorem postcomp_extClass_surjective_of_projective_X₂ [Small.{v} R]
    {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (M : ModuleCat.{v} R) (n : Nat)
    [Injective S.X₂] : Function.Surjective (h.extClass.postcomp M (rfl : n + 1 = n + 1)) :=
  fun x => Ext.covariant_sequence_exact₁ M h x (Ext.eq_zero_of_injective _) rfl
