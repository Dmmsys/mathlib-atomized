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
/-- Transfer a `TopologicalSpace` across an `Equiv` -/
/-
**Equiv.topologicalSpace** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [TopologicalSpace β] → α ≃ β → Topologic
alSpace α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer a `TopologicalSpace` across an `Equiv`
-/
protected abbrev topologicalSpace [TopologicalSpace β] (e : α ≃ β) :
    TopologicalSpace α :=
  .induced e.toFun ‹_›

/-- An equivalence `e : α ≃ β` gives a homeomorphism `α ≃ₜ β` where the topological space structure
on `α` is the one obtained by transporting the topological space structure on `β` back along `e`. -/
/-
**Equiv.homeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：homeomorph [TopologicalSpace β] (e : α ≃ β) : letI
参数：e : α ≃ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence `e : α ≃ β` gives a homeomorphism `α ≃ₜ β` where the topological 
space structure
on `α` is the one obtained by transporting the topological space structure on `β
` back along `e`.
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

