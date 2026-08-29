/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Bhavik Mehta, Thomas Browning
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Compact operators and finite dimensional spaces

This file contains results linking `IsCompactOperator` with `FiniteDimensional`.

The motivation for not including this in the same file as the definition of compact operators
is that `Mathlib.Topology.Algebra.Module.FiniteDimension` is quite a heavy import to add there.
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/--
theorem `isCompactOperator_id_iff_finiteDimensional` / 定理 `isCompactOperator_id_iff_finiteDimensional`

English:
theorem isCompactOperator_id_iff_finiteDimensional
  given: [LocallyCompactSpace 𝕜]
  proof: isCompactOperator_id_iff_locallyCompactSpace.trans
    ⟨fun _ => .of_locallyCompactSpace 𝕜, fun _ => .of_finiteDimensional_of_complete 𝕜 E⟩

中文:
定理 isCompactOperator_id_iff_finiteDimensional
  条件: [LocallyCompactSpace 𝕜]
  证明: isCompactOperator_id_iff_locallyCompactSpace.trans
    ⟨fun _ => .of_locallyCompactSpace 𝕜, fun _ => .of_finiteDimensional_of_complete 𝕜 E⟩

Depends on / 依赖: isCompactOperator_id_iff_locallyCompactSpace, isCompactOperator_id_iff_locallyCompactSpace.trans, of_finiteDimensional_of_complete, of_locallyCompactSpace
-/
theorem isCompactOperator_id_iff_finiteDimensional [LocallyCompactSpace 𝕜] :
    IsCompactOperator (_root_.id : E -> E) ↔ FiniteDimensional 𝕜 E :=
  isCompactOperator_id_iff_locallyCompactSpace.trans
    ⟨fun _ => .of_locallyCompactSpace 𝕜, fun _ => .of_finiteDimensional_of_complete 𝕜 E⟩

/--
lemma `FiniteDimensional.of_isCompactOperator_id` / 引理 `FiniteDimensional.of_isCompactOperator_id`

English:
lemma FiniteDimensional.of_isCompactOperator_id
  given: (h : IsCompactOperator (id : E -> E))
  proof: by
  have := LocallyCompactSpace.of_isCompactOperator_id h
  exact FiniteDimensional.of_locallyCompactSpace 𝕜

@[deprecated (since := "2026-03-05")] alias IsCompactOperator.finiteDimensional :=
  FiniteDimensional.of_isCompactOperator_id

中文:
引理 FiniteDimensional.of_isCompactOperator_id
  条件: (h : IsCompactOperator (id : E -> E))
  证明: by
  have := LocallyCompactSpace.of_isCompactOperator_id h
  exact FiniteDimensional.of_locallyCompactSpace 𝕜

@[deprecated (since := "2026-03-05")] alias IsCompactOperator.finiteDimensional :=
  FiniteDimensional.of_isCompactOperator_id

Depends on / 依赖: FiniteDimensional, FiniteDimensional.of_locallyCompactSpace, LocallyCompactSpace, LocallyCompactSpace.of_isCompactOperator_id, of_isCompactOperator_id, of_locallyCompactSpace
-/
lemma FiniteDimensional.of_isCompactOperator_id (h : IsCompactOperator (id : E -> E)) :
    FiniteDimensional 𝕜 E := by
  have := LocallyCompactSpace.of_isCompactOperator_id h
  exact FiniteDimensional.of_locallyCompactSpace 𝕜

@[deprecated (since := "2026-03-05")] alias IsCompactOperator.finiteDimensional :=
  FiniteDimensional.of_isCompactOperator_id
