/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Basic facts about algebra representations

This file collects basic general facts about algebra representations. The purpose of this file is
to have general results so that when we prove a corresponding fact about group representations
(or Lie algebra representations etc), we can deduce them as special cases of facts from this file.

-/

public section

variable {A V : Type*} (k : Type*) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [Module A V] [IsScalarTower k A V]
  [IsSimpleModule A V] [FiniteDimensional k V] [IsAlgClosed k]

/--
theorem `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed` / 定理 `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`

English:
theorem IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
  proof: by
have : Module.Finite k (Module.End A V) := .of_injective (LinearMap.restrictScalarsₗ k A V V k)
    LinearMap.restrictScalars_injective _
  classical exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)

中文:
定理 IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
  证明: by
have : Module.Finite k (Module.End A V) := .of_injective (LinearMap.restrictScalarsₗ k A V V k)
    LinearMap.restrictScalars_injective _
  classical exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)

Depends on / 依赖: Finite, IsAlgClosed, IsAlgClosed.algebraMap_bijective_of_isIntegral, LinearMap, LinearMap.restrictScalars, LinearMap.restrictScalars_injective, Module, Module.End, Module.Finite, algebraMap_bijective_of_isIntegral, classical, of_injective, restrictScalars_injective
-/
theorem IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed :
    Function.Bijective (algebraMap k (Module.End A V)) := by
have : Module.Finite k (Module.End A V) := .of_injective (LinearMap.restrictScalarsₗ k A V V k)
    LinearMap.restrictScalars_injective _
  classical exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)

variable (A V)

open scoped IsMulCommutative in
/--
theorem `IsSimpleModule.finrank_eq_one_of_isMulCommutative` / 定理 `IsSimpleModule.finrank_eq_one_of_isMulCommutative`

English:
theorem IsSimpleModule.finrank_eq_one_of_isMulCommutative
  given: [IsMulCommutative A]
  proof: by
  have : Nontrivial V := IsSimpleModule.nontrivial A V
  obtain ⟨v, v_nz⟩ := exists_ne (0 : V)
  set U : Submodule A V := { Submodule.span k {v} with
    smul_mem' a w hw := by
      have ⟨t, ht⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).2
        (Module.toModuleEnd A V a)
  

中文:
定理 IsSimpleModule.finrank_eq_one_of_isMulCommutative
  条件: [IsMulCommutative A]
  证明: by
  have : Nontrivial V := IsSimpleModule.nontrivial A V
  obtain ⟨v, v_nz⟩ := exists_ne (0 : V)
  set U : Submodule A V := { Submodule.span k {v} with
    smul_mem' a w hw := by
      have ⟨t, ht⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).2
        (Module.toModuleEnd A V a)
  

Depends on / 依赖: IsSimpleModule, IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed, IsSimpleModule.nontrivial, Module, Module.toModuleEnd, Nontrivial, Submodule, Submodule.mem_span_singleton_self, Submodule.span, algebraMap_end_bijective_of_isAlgClosed, eq_bot_or_eq_top, exists_ne, finrank_eq_one_iff_of_nonzero, hU.le, mem_span_singleton_self, nontrivial, smul_mem, toModuleEnd, v_nz
-/
theorem IsSimpleModule.finrank_eq_one_of_isMulCommutative [IsMulCommutative A] :
    Module.finrank k V = 1 := by
  have : Nontrivial V := IsSimpleModule.nontrivial A V
  obtain ⟨v, v_nz⟩ := exists_ne (0 : V)
  set U : Submodule A V := { Submodule.span k {v} with
    smul_mem' a w hw := by
      have ⟨t, ht⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).2
        (Module.toModuleEnd A V a)
      simpa only [← show _ = a • w from congr($ht w)] using! (k ∙ v).smul_mem t hw }
  obtain hU | hU := eq_bot_or_eq_top U
  · exact (v_nz <| hU.le <| Submodule.mem_span_singleton_self v).elim
  · rw [finrank_eq_one_iff_of_nonzero v v_nz]
    rwa [← top_le_iff] at hU ⊢
