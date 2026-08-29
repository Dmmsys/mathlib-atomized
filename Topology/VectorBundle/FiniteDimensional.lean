/-
Copyright (c) 2026 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Finite-rank vector bundles -/

public section

namespace VectorBundle

open Bundle FiberBundle

variable (R : Type*) {B : Type*} (F : Type*) (E : B -> Type*)
  [NontriviallyNormedField R] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)]
  [NormedAddCommGroup F] [NormedSpace R F]
  [(x : B) -> TopologicalSpace (E x)] [FiberBundle F E]
  [(x : B) -> AddCommGroup (E x)] [(x : B) -> Module R (E x)] [VectorBundle R F E]

include E F

/--
lemma `finiteDimensional` / 引理 `finiteDimensional`

English:
lemma finiteDimensional
  given: (b : B) [FiniteDimensional R F]
  statement: FiniteDimensional R (E b)
  proof: (continuousLinearEquivAt R F E b).symm.finiteDimensional

中文:
引理 finiteDimensional
  条件: (b : B) [FiniteDimensional R F]
  结论: FiniteDimensional R (E b)
  证明: (continuousLinearEquivAt R F E b).symm.finiteDimensional
-/
protected lemma finiteDimensional (b : B) [FiniteDimensional R F] : FiniteDimensional R (E b) :=
  (continuousLinearEquivAt R F E b).symm.finiteDimensional

/--
lemma `finrank_eq` / 引理 `finrank_eq`

English:
lemma finrank_eq
  given: (b : B)
  statement: Module.finrank R (E b) = Module.finrank R F
  proof: (continuousLinearEquivAt R F E b).finrank_eq

中文:
引理 finrank_eq
  条件: (b : B)
  结论: Module.finrank R (E b) = Module.finrank R F
  证明: (continuousLinearEquivAt R F E b).finrank_eq
-/
protected lemma finrank_eq (b : B) : Module.finrank R (E b) = Module.finrank R F :=
  (continuousLinearEquivAt R F E b).finrank_eq

end VectorBundle
