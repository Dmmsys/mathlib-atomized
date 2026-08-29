/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# A module over a division ring is simple iff it has rank one
-/

public section

/--
theorem `isSimpleModule_iff_finrank_eq_one` / 定理 `isSimpleModule_iff_finrank_eq_one`

English:
theorem isSimpleModule_iff_finrank_eq_one
  given: {R M} [DivisionRing R] [AddCommGroup M] [Module R M]
  proof: ⟨fun h => have := h.nontrivial; have ⟨v, hv⟩ := exists_ne (0 : M)
    (finrank_eq_one_iff_of_nonzero' v hv).mpr (IsSimpleModule.toSpanSingleton_surjective R hv),
  (isSimpleModule_iff ..).mpr ∘ is_simple_module_of_finrank_eq_one⟩

中文:
定理 isSimpleModule_iff_finrank_eq_one
  条件: {R M} [除环 R] [加法交换群 M] [模 R M]
  证明: ⟨fun h => have := h.nontrivial; have ⟨v, hv⟩ := exists_ne (0 : M)
    (finrank_eq_one_iff_of_nonzero' v hv).mpr (IsSimpleModule.toSpanSingleton_surjective R hv),
  (isSimpleModule_iff ..).mpr ∘ is_simple_module_of_finrank_eq_one⟩

Depends on / 依赖: IsSimpleModule, IsSimpleModule.toSpanSingleton_surjective, exists_ne, finrank_eq_one_iff_of_nonzero, h.nontrivial, isSimpleModule_iff, is_simple_module_of_finrank_eq_one, nontrivial, toSpanSingleton_surjective
-/
theorem isSimpleModule_iff_finrank_eq_one {R M} [DivisionRing R] [AddCommGroup M] [Module R M] :
    IsSimpleModule R M ↔ Module.finrank R M = 1 :=
  ⟨fun h => have := h.nontrivial; have ⟨v, hv⟩ := exists_ne (0 : M)
    (finrank_eq_one_iff_of_nonzero' v hv).mpr (IsSimpleModule.toSpanSingleton_surjective R hv),
  (isSimpleModule_iff ..).mpr ∘ is_simple_module_of_finrank_eq_one⟩
