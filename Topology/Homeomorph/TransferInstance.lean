/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Topology.Homeomorph.Defs

/-!
# Transfer topological structure across `Equiv`s

We show how to transport a topological space structure across an `Equiv` and prove that this
make the equivalence a homeomorphism between the original space and the transported topology.

-/

@[expose] public section

variable {R α β : Type*}

namespace Equiv

-- See note [instance transfer via equivalence]
/--
Definition of `topologicalSpace` / `topologicalSpace` 的定义

English:
abbreviation topologicalSpace
  signature: [TopologicalSpace β] (e : α ≃ β)
  body: .induced e.toFun ‹_›

中文:
缩写 topologicalSpace
  签名: [TopologicalSpace β] (e : α ≃ β)
  定义体: .induced e.toFun ‹_›
-/
protected abbrev topologicalSpace [TopologicalSpace β] (e : α ≃ β) :
    TopologicalSpace α :=
  .induced e.toFun ‹_›

/--
Definition of `homeomorph` / `homeomorph` 的定义

English:
definition homeomorph
  signature: [TopologicalSpace β] (e : α ≃ β)
  body: e.topologicalSpace
    α ≃ₜ β :=
  letI := e.topologicalSpace
  { e with
    continuous_toFun := continuous_induced_dom
    continuous_invFun := by
      simp only [Equiv.invFun_as_coe]
      convert! continuous_coinduced_rng
      rw [e.coinduced_symm]
      rfl }

中文:
定义 homeomorph
  签名: [TopologicalSpace β] (e : α ≃ β)
  定义体: e.topologicalSpace
    α ≃ₜ β :=
  letI := e.topologicalSpace
  { e with
    continuous_toFun := continuous_induced_dom
    continuous_invFun := by
      simp only [Equiv.invFun_as_coe]
      convert! continuous_coinduced_rng
      rw [e.coinduced_symm]
      rfl }

Depends on / 依赖: e.topologicalSpace, topologicalSpace
-/
def homeomorph [TopologicalSpace β] (e : α ≃ β) :
    letI := e.topologicalSpace
    α ≃ₜ β :=
  letI := e.topologicalSpace
  { e with
    continuous_toFun := continuous_induced_dom
    continuous_invFun := by
      simp only [Equiv.invFun_as_coe]
      convert! continuous_coinduced_rng
      rw [e.coinduced_symm]
      rfl }

end Equiv
